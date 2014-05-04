package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._
import scala.None
import java.util.Date

/**
 * This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  
  lexical.reserved ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
    "pred", "iszero", "let", "in", "fst", "snd")

  /**
   * Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = positioned(
    rep1(SimpleTerm) ^^ { case termList => parseTermList(termList) }
      | failure("illegal start of term"))

  /**
   * SimpleTerm ::= "true"
   *               | "false"
   *               | number
   *               | "succ" Term
   *               | "pred" Term
   *               | "iszero" Term
   *               | "if" Term "then" Term "else" Term
   *               | ident
   *               | "\" ident ":" Type "." Term
   *               | "(" Term ")"
   *               | "let" ident ":" Type "=" Term "in" Term
   *               | "{" Term "," Term "}"
   *               | "fst" Term
   *               | "snd" Term
   */
  def SimpleTerm: Parser[Term] = positioned(
    "true" ^^^ True
      | "false" ^^^ False
      | nv
      | "succ" ~> Term ^^ {
        case e1 => Succ(e1)
      }
      | "pred" ~> Term ^^ {
        case e1 => Pred(e1)
      }
      | "iszero" ~> Term ^^ {
        case e1 => IsZero(e1)
      }
      | "let" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^ {
        case "let" ~ x ~ ":" ~ tType ~ "=" ~ t1 ~ "in" ~ t2 =>
          Application(TermPar(Abstraction(Variable(x), tType, t2)), t1)
      }
      | "if" ~ Term ~ "then" ~ Term ~ "else" ~ Term ^^ {
        case ("if" ~ t1 ~ "then" ~ t2 ~ "else" ~ t3) =>
          IfThenElse(t1, t2, t3)
      }
      | ident ^^ { case x => Variable(x.toString) }
      | "\\" ~ ident ~ ":" ~ Type ~ "." ~ Term ^^ {
        case "\\" ~ x ~ ":" ~ t ~ "." ~ t1 =>
          Abstraction(Variable(x.toString), t, t1)
      }
      | "(" ~ Term ~ ")" ^^ {
        case "(" ~ t ~ ")" => TermPar(t)
      }
      | "{" ~ Term ~ "," ~ Term ~ "}" ^^ {
        case "{" ~ t1 ~ "," ~ t2 ~ "}" => Pair(t1, t2)
      }
      | "fst" ~ Term ^^ { case "fst" ~ t => Fst(t) }
      | "snd" ~ Term ^^ { case "snd" ~ t => Snd(t) }
      | failure("illegal start of simple term"))

  def nv: Parser[Term] = positioned(
    rep("succ") ~ numericLit ^^ {
      case list ~ numLit => syntacticSugar(list.size + numLit.toInt)
    }
      | failure("illegal start of simple term"))

  def syntacticSugar(x: Int): Term = {
    x match {
      case t if t == 0 => Zero
      case _ => Succ(syntacticSugar(x - 1))
    }
  }

  /**
   * Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] = positioned(
    PairType ~ rep("->" ~ PairType) ^^ { case t1 ~ list => parserTypeList(t1, list.map { _._2 }, true) }
      | failure("illegal start of type"))

  def PairType: Parser[Type] = positioned(
    SType ~ rep("*" ~ SType) ^^ { case t1 ~ list => parserTypeList(t1, list.map { _._2 }, false) }
      | failure("illegal start of type"))

  def SType: Parser[Type] = positioned(
    "Nat" ^^^ TypeNat
      | "Bool" ^^^ TypeBool
      | "(" ~ Type ~ ")" ^^ {
        case "(" ~ t ~ ")" => t match {
          case TypePar(x) => t
          case _ => TypePar(t)
        }
      }
      | failure("illegal start of type"))

  def parseTermList(termList: List[Term]): Term = {
    termList match {
      case head :: Nil => head
      case _ => Application(parseTermList(termList.init), termList.last)
    }
  }

  def parserTypeList(first: Type, typeList: List[Type], isFun: Boolean): Type = typeList match {
    case head :: Nil => if (isFun) TypeFun(first, head) else TypePair(first, head)
    case head :: tail => {
      if (isFun) TypeFun(first, parserTypeList(head, tail, isFun))
      else TypePair(first, parserTypeList(head, tail, isFun))
    }
    case nil => first
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(pos: Position, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + pos.longString
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Is the given term a numeric value? */
  def isNumericVal(t: Term): Boolean = t match {
    case Zero => true
    case TermPar(x) => isNumericVal(x)
    case Succ(x) => isNumericVal(x)
    case _ => false
  }

  /** Is the given term a value? */
  def isValue(t: Term): Boolean = t match {
    case _: Value | TermPar(_: Value) => true
    case Pair(t1, t2) => { isValue(t1) && isValue(t2) }
    case _ => isNumericVal(t)
  }

  def alpha(t: Abstraction): Abstraction = {
    val newVarName = t.x.name + "$"
    var i = 1
    while (t.fv contains (newVarName + i)) {
      i += 1
    }
    val newVar = Variable(newVarName + i)
    Abstraction(newVar, t.tType, subst(t.t, t.x.name, newVar))
  }

  /**
   * Substitute into term t all occurrences of x with s
   */
  def subst(t: Term, x: String, s: Term): Term = t match {
    case Variable(n) => {
      if (n == x) s
      else t
    }
    case Abstraction(varBind, absType, b) => {
      if (varBind.name == x) t
      else {
        if (s.fv contains varBind.name) {
          val t1 = alpha(t.asInstanceOf[Abstraction])
          Abstraction(t1.x, t1.tType, subst(t1.t, x, s))
        } else {
          Abstraction(varBind, t.asInstanceOf[Abstraction].tType, subst(b, x, s))
        }
      }
    }
    case IsZero(numVal) => IsZero(subst(numVal, x, s))
    case Pred(numVal) => Pred(subst(numVal, x, s))
    case Succ(numVal) => Succ(subst(numVal, x, s))
    case Pair(t1, t2) => Pair(subst(t1, x, s), subst(t2, x, s))
    case Fst(numVal) => Fst(subst(numVal, x, s))
    case Snd(numVal) => Snd(subst(numVal, x, s))
    case IfThenElse(t1, t2, t3) => IfThenElse(subst(t1, x, s), subst(t2, x, s), subst(t3, x, s))
    case Application(t1, t2) => Application(subst(t1, x, s), subst(t2, x, s))
    case TermPar(termPar) => TermPar(subst(termPar, x, s))
    case _ => t
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case _ if isValue(t) => throw NoRuleApplies(t)
    case Succ(x) => Succ(reduce(x))
    case Pred(x) => x match {
      case TermPar(inner) if (isNumericVal(inner)) => reduce(Pred(inner))
      case Zero => Zero
      case Succ(numVal) if isNumericVal(numVal) => numVal
      case _ => Pred(reduce(x))
    }
    case IsZero(x) => x match {
      case TermPar(inner) if (isNumericVal(inner)) => reduce(IsZero(inner))
      case Zero => True
      case Succ(numVal) if isNumericVal(numVal) => False
      case _ => IsZero(reduce(x))
    }
    case IfThenElse(t1, t2, t3) => t1 match {
      case TermPar(inner) if (isValue(inner)) => reduce(IfThenElse(inner, t2, t3))
      case True => t2
      case False => t3
      case _ => IfThenElse(reduce(t1), t2, t3)
    }
    case Fst(x) => x match {
      case TermPar(inner) if (isValue(inner)) => reduce(Fst(inner))
      case Pair(x1, x2) if isValue(x) => x1
      case _ => Fst(reduce(x))
    }
    case Snd(x) => x match {
      case TermPar(inner) if (isValue(inner)) => reduce(Snd(inner))
      case Pair(x1, x2) if isValue(x) => x2
      case _ => Snd(reduce(x))
    }
    case TermPar(inner) => TermPar(reduce(inner))
    case p: Pair => isValue(p.t1) match {
      case false => Pair(reduce(p.t1), p.t2)
      case true => Pair(p.t1, reduce(p.t2))
    }
    case Application(t1, t2) => t1 match {
      case TermPar(inner) if (isValue(inner)) => isValue(t2) match {
        case true => TermPar(reduce(Application(inner, t2)))
        case false => Application(t1, reduce(t2))        
      }
      case Abstraction(x, _, b) => isValue(t2) match {
        case true => subst(b, x.name, t2)
        case false => Application(t1, reduce(t2))
      }
      case _ => {
        Application(reduce(t1), t2)
      }
    }
    case _ => throw NoRuleApplies(t)
  }

  def contextLookup(ctx: Context, name: String): Type = {
    ctx.find({ e => e._1 == name }) match {
      case Some(x) =>
        x._2
      case None => null
    }
  }

  def addToContext(ctx: Context, name: String, t: Type): Context = {
    // just add the variable
    List((name, t)) ::: ctx
  }
  
  def renameVar(t: Abstraction, ctx: Context): Abstraction = {
    val newVarName = t.x.name + "$"
    var i = 1
    while ((t.fv contains (newVarName + i)) || contextLookup(ctx, newVarName + i) != null) {
      i += 1
    }
    val newVar = Variable(newVarName + i)
    Abstraction(newVar, t.tType, subst(t.t, t.x.name, newVar))
  }

  /**
   * Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True | False | Zero =>
      t.getTermType
    case Succ(x) => {
      val argType = typeof(ctx, x)
      if (argType == TypeNat) {
        TypeNat
      } else {
        throw new TypeError(t.pos, "expected: Nat, found: " + argType)
      }
    }
    case Pred(x) => {
      val argType = typeof(ctx, x)
      if (argType == TypeNat) {
        TypeNat
      } else {
        throw new TypeError(t.pos, "expected: Nat, found: " + argType)
      }
    }
    case IsZero(x) => {
      val argType = typeof(ctx, x)
      if (argType == TypeNat) {
        TypeBool
      } else {
        throw new TypeError(t.pos, "expected: Nat, found: " + argType)
      }
    }
    case IfThenElse(t1, t2, t3) => typeof(ctx, t1) match {
      case TypeBool => {
        val t2Type = typeof(ctx, t2)
        val t3Type = typeof(ctx, t3)
        if (t2Type == t3Type) {
          t2Type
        } else {
          throw TypeError(t.pos, "type mismatch between conditional branches")
        }
      }
      case notBool => throw TypeError(t.pos, "expected: Bool, found: " + notBool)
    }
    case Variable(x) => {
      val varType = contextLookup(ctx, x)
      if (null == varType) {
        throw TypeError(t.pos, "undefined variable " + x)
      }
      varType
    }
    case Fst(x) => {
      val pairType = typeof(ctx, x)
      pairType match {
        case TypePair(p1, p2) => p1
        case _ => throw TypeError(t.pos, "pair type expected but " + pairType + " found")
      }
    }
    case Snd(x) => {
      val pairType = typeof(ctx, x)
      pairType match {
        case TypePair(p1, p2) => p2
        case _ => throw TypeError(t.pos, "pair type expected but " + pairType + " found")
      }
    }
    case TermPar(x) => typeof(ctx, x)
    case Application(t1, t2) => {
      val t1Type = typeof(ctx, t1)
      t1Type match {
        case TypePar(inner) => typeof(ctx, Application(inner, t2))
        case TypeFun(t1Fun, t2Fun) => {
          val t2Type = typeof(ctx, t2)
          if (t1Fun == t2Type) {
            t2Fun
          } else {
            throw TypeError(t.pos, "expected: " + t1Fun + ", found: " + t2Type)
          }
        }
        case notFun => throw TypeError(t.pos, "expected: function type, found: " + t1Type)
      }
    }
    case a:Abstraction => a.x match {
      case Variable(name) => {
        if (contextLookup(ctx, name) != null) {
          val renamed = renameVar(a, ctx)
          a.x = renamed.x
          a.t = renamed.t       
        }
        val newContext = addToContext(ctx, a.x.name, a.tType)       
        val bodyType = typeof(newContext, a.t)
        TypeFun(a.tType, bodyType)
      }
      case _ => throw TypeError(t.pos, "How did I parse this?!#@?! -.-")
    }
    case Pair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
    case _ => throw TypeError(t.pos, "This is not Term type " + t)
  }

  /**
   * Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      t1 match {
        case TermPar(inner) => Stream.cons(t, path(inner, reduce))
        case _ => Stream.cons(t, path(t1, reduce))
      }      
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val tokens = new lexical.Scanner("\\x:Nat.\\x:Nat.\\x:Nat.x")
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          Application.keepPar = false
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Throwable => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
