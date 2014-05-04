package fos

import scala.collection.immutable.List
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import java.util.LinkedList
import scala.util.parsing.input.StreamReader

/**
 * This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers with PackratParsers{
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  
  def AbsVar: Parser[AbsVar] = (
      ident ^^ {case e => Variable(e)}
      | "\\" ~ ident ~ "." ~ Term ^^ {case "\\" ~ e1 ~ "." ~ e2 => Abstraction(Variable(e1), e2)}
      | "(" ~> AbsVar <~ ")" ^^ {case e => e.copyAndSetParen().asInstanceOf[AbsVar]}
  )
  /**
   * Term     ::= AbsOrVar { AbsOrVar }
   */
   def Term: Parser[Term] = (
       rep1(AbsVar) ~ rep(Term) ^^ {case absVarList ~ termList => {
         makeTerm(absVarList ++ chopTerms(termList))}
       }
       | "(" ~ Term ~ ")" ~ rep(Term) ^^ {case "(" ~ t ~ ")" ~ termList => {
         makeTerm(t.copyAndSetParen() +: chopTerms(termList))}
       }
       | failure("illegal start of term")
   )
   
   def chopTerms(termList: List[Term]): List[Term] = {
    var chopedTerms = List[Term]()
    for(t <- termList) t match {
      case Variable(_) => chopedTerms = chopedTerms :+ t
      case Abstraction(_, _, _) => chopedTerms = chopedTerms :+ t
      case Application(t1, t2, true) => chopedTerms = chopedTerms :+ t
      case Application(t1, t2, false) => chopedTerms = chopedTerms ++ chopTerms(List(t1)) ++ chopTerms(List(t2))
    }
    chopedTerms
  }

   def makeTerm(termList: List[Term]):Term = {
    
    if(termList.size == 1) {
      termList(0)
    } else {
      var app = Application(termList(0), termList(1))
      for(i <- 2 until termList.size) {
        app = Application(app, termList(i))
      }
      app
    }
  }

  /** Term 't' does not match any reduction rule. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)
  
  def alpha(t: Term): Term = {
    val free_vars = t.fv
    val a = t.asInstanceOf[Abstraction]
    
    val new_var_name = a.x.name + "$"
    var i = 1
    while (free_vars contains (new_var_name + i)) {
      i+=1
    }
    
    val new_var = Variable(new_var_name + i) 
    Abstraction(new_var, subst(a.t, a.x.name, new_var))
  }
  
  def subst(t: Term, x: String, s: Term): Term = t match{
    case Variable(n) => {
      if (n == x) s
      else t
    }
    case Abstraction(v, b, _) => {
      if (v.name == x) t
      else {
	      if(s.fv contains v.name) {
	        val t1 = alpha(t).asInstanceOf[Abstraction]
	        Abstraction(t1.x, subst(t1.t, x, s), t.hasParenthesis)
	      } else {
	    	Abstraction(v, subst(b, x, s), t.hasParenthesis)
	      }
      }
    }
    case Application(t1, t2, _) => Application(subst(t1, x, s), subst(t2, x, s), t.hasParenthesis)
    case _ => t
  }
  
  def tryReduce(t:Term, reduce: Term => Term): Term = {
    try {
      reduce(t)
    } catch {
		case NoRuleApplies(_) => null
	}
  }
  
  def adaptParenthesis(o:Term, n:Term): Term = {
    if(o.hasParenthesis) {
      n.copyAndSetParen(true)
    } else {
      n
    }
  }
  
  /**
   * Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = t match {
    case Application(t1, t2, _) => t1 match {
      case Abstraction(x, b, _) => adaptParenthesis(t1, subst(b, x.name, t2))
      case _ => {
        val t1Red = tryReduce(t1, reduceNormalOrder)
        if (t1Red != null) {
          adaptParenthesis(t, Application(t1Red, t2))
        } else {
          val t2Red = tryReduce(t2, reduceNormalOrder)
          if (t2Red != null) {
            adaptParenthesis(t, Application(t1, t2Red))
          } else {
            throw NoRuleApplies(t)
          }
        } 
      }
    }
    case Abstraction(x, b, p) => adaptParenthesis(t, Abstraction(x, reduceNormalOrder(b), p))
    case _ => throw NoRuleApplies(t)
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term = t match {
     case Application(t1, t2, _) => t1 match {
      case Abstraction(x, b, _) => {
        if (t2.isValue) {
          //3. rule
          adaptParenthesis(t1, subst(b, x.name, t2)) 
        }
        else {
          //2. rule
          val t2Red = tryReduce(t2, reduceCallByValue)	
          if (t2Red != null) {
        	adaptParenthesis(t, Application(t1, t2Red))
          } else {
        	throw NoRuleApplies(t)
          }
        }
      }
      case _ => {
        //1. rule
        val t1Red = tryReduce(t1, reduceCallByValue)
        if (t1Red != null) {
          adaptParenthesis(t, Application(t1Red, t2))
        } else {
            throw NoRuleApplies(t)
        }
      }
    }
    case _ => throw NoRuleApplies(t)
  }

  /**
   * Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t).copyAndSetParen(false)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val tokens = new lexical.Scanner("(\\x.\\y.x y) (\\h.y z)")
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        fos.Term.keepParenthesis = false
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder)) 
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)
      case e =>
        println(e)
    }
  }
}