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
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "=>", "->", "{", "}", ",", "*", "+", "|")
  lexical.reserved ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
    "pred", "iszero", "let", "in", "fst", "snd", "case", "inr", "inl", "of", "as", "letrec", "fix")

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
      | "(" ~> Term <~ ")" ^^ {
        case t => TermPar(t)
      }
      | "{" ~ Term ~ "," ~ Term ~ "}" ^^ {
        case "{" ~ t1 ~ "," ~ t2 ~ "}" => Pair(t1, t2)
      }
      | "fst" ~> Term ^^ { case t => Fst(t) }
      | "snd" ~> Term ^^ { case t => Snd(t) }
      | extensions
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

  def extensions: Parser[Term] = positioned(
    "inl" ~ Term ~ "as" ~ Type ^^ { case "inl" ~ t ~ "as" ~ tType => Inl(t, tType) }
      | "inr" ~ Term ~ "as" ~ Type ^^ { case "inr" ~ t ~ "as" ~ tType => Inr(t, tType) }
      | "case" ~ Term ~ "of" ~ "inl" ~ ident ~ "=>" ~ Term ~ "|" ~ "inr" ~ ident ~ "=>" ~ Term ^^
      {
        case "case" ~ t ~ "of" ~ "inl" ~ x1 ~ "=>" ~ t1 ~ "|" ~ "inr" ~ x2 ~ "=>" ~ t2 =>
          Case(t, Variable(x1), t1, Variable(x2), t2)
      }
      | "fix" ~> Term ^^ { case t => Fix(t) }
      | "letrec" ~ ident ~ ":" ~ Type ~ "=" ~ Term ~ "in" ~ Term ^^ {
        case "letrec" ~ x ~ ":" ~ xType ~ "=" ~ t1 ~ "in" ~ t2 =>
          Application(TermPar(Abstraction(Variable(x), xType, t2)), Fix(TermPar(Abstraction(Variable(x), xType, t1))))
      })

  /**
   * Type       ::= SimpleType [ "->" Type ]
   */
  def Type: Parser[Type] = positioned(
    TupleType ~ rep("->" ~ TupleType) ^^ { case t1 ~ list => parseTypes(t1, list.map { i => (i._1, i._2) }) }
      | failure("illegal start of type"))

  def TupleType: Parser[Type] = positioned(
    SType ~ rep(("*" | "+") ~ SType) ^^ { case t1 ~ list => parseTypes(t1, list.map { i => (i._1, i._2) }) })

  def SType: Parser[Type] = positioned(
    "Nat" ^^^ TypeNat
      | "Bool" ^^^ TypeBool
      | "(" ~> Type <~ ")" ^^ {
        case t => t match {
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

  def parseTypes(first: Type, typeList: List[Tuple2[String, Type]]): Type = typeList match {
    case head :: Nil => head._1 match {
      case "->" => TypeFun(first, head._2)
      case "+" => TypeSum(first, head._2)
      case "*" => TypePair(first, head._2)
    }
    case head :: tail => head._1 match {
      case "->" => TypeFun(first, parseTypes(head._2, tail))
      case "+" => TypeSum(first, parseTypes(head._2, tail))
      case "*" => TypePair(first, parseTypes(head._2, tail))
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
    case TermPar(inner) => isValue(inner)
    case Pair(t1, t2) => { isValue(t1) && isValue(t2) }
    case Inr(t, _) => isValue(t)
    case Inl(t, _) => isValue(t)
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
    case a: Abstraction => {
      if (a.x.name == x) t
      else {
        if (s.fv contains a.x.name) {
          val a1 = alpha(a)
          Abstraction(a1.x, a1.tType, subst(a1.t, x, s))
        } else {
          Abstraction(a.x, a.tType, subst(a.t, x, s))
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
    case Case(caseTerm, x1, t1, x2, t2) => Case(subst(caseTerm, x, s), x1, subst(t1, x, s), x2, subst(t2, x, s))
    case Inl(inlTerm, inlType) => Inl(subst(inlTerm, x, s), inlType)
    case Inr(inrTerm, inrType) => Inr(subst(inrTerm, x, s), inrType)
    case Fix(t) => Fix(subst(t, x, s))
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
      case TermPar(Abstraction(x, _, b)) => isValue(t2) match {
        case true => TermPar(subst(b, x.name, t2))
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
    case Case(caseTerm, x1, t1, x2, t2) => caseTerm match {
      case _ if isValue(caseTerm) => caseTerm match {
        case Inl(inlVal, _) => subst(t1, x1.name, inlVal)
        case Inr(inrVal, _) => subst(t2, x2.name, inrVal)
        case TermPar(inner) => reduce(Case(inner, x1, t1, x2, t2))
      }
      case _ => Case(reduce(caseTerm), x1, t1, x2, t2)
    }
    case Inl(inlTerm, inlType) => Inl(reduce(inlTerm), inlType)
    case Inr(inrTerm, inrType) => Inr(reduce(inrTerm), inrType)
    case Fix(t1) => t1 match {
      case Abstraction(x, xType, body) => body match {
        case bodyAbs: Abstraction => subst(alpha(bodyAbs), x.name, Fix(TermPar(t1)))
        case _ => subst(body, x.name, Fix(TermPar(t1)))
      }
      case TermPar(Abstraction(x, xType, body)) => body match {
        case bodyAbs: Abstraction => subst(alpha(bodyAbs), x.name, t)
        case _ => subst(body, x.name, t)
      }
      case _ => Fix(reduce(t1))
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

  def renameVar(varName: String, body: Term, ctx: Context): Tuple2[String, Term] = {
    val newVarName = varName + "$"
    var i = 1
    while (((body.fv - varName) contains (newVarName + i)) || contextLookup(ctx, newVarName + i) != null) {
      i += 1
    }
    val newVar = Variable(newVarName + i)
    (newVar.name, subst(body, varName, newVar))
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
        case TypePar(TypeFun(t1Fun, t2Fun)) => {
          val t2Type = typeof(ctx, t2)
          if (t1Fun == t2Type) {
            t2Fun
          } else {
            throw TypeError(t.pos, "expected: " + t1Fun + ", found: " + t2Type)
          }
        }
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
    case a: Abstraction => a.x match {
      case Variable(name) => {
        if (contextLookup(ctx, name) != null) {
          val renamed = renameVar(a.x.name, a.t, ctx)
          a.x = Variable(renamed._1)
          a.t = renamed._2
        }
        val newContext = addToContext(ctx, a.x.name, a.tType)
        val bodyType = typeof(newContext, a.t)
        TypeFun(a.tType, bodyType)
      }
      case _ => throw TypeError(t.pos, "How did I parse this?!#@?! -.-")
    }
    case Pair(t1, t2) => TypePair(typeof(ctx, t1), typeof(ctx, t2))
    case c: Case => {
      if (contextLookup(ctx, c.x1.name) != null) {
        val renamed = renameVar(c.x1.name, c.t1, ctx)
        c.x1 = Variable(renamed._1)
        c.t1 = renamed._2
      }
      if (contextLookup(ctx, c.x2.name) != null) {
        val renamed = renameVar(c.x2.name, c.t2, ctx)
        c.x2 = Variable(renamed._1)
        c.t2 = renamed._2
      }
      val tType = typeof(ctx, c.t)
      tType match {
        case TypeSum(sumType1, sumType2) => {
          val t1Type = typeof(addToContext(ctx, c.x1.name, sumType1), c.t1)
          val t2Type = typeof(addToContext(ctx, c.x2.name, sumType2), c.t2)
          if (t1Type == t2Type) {
            t1Type
          } else {
            throw TypeError(t.pos, "case types do not match, found: " + t1Type + " and " + t2Type)
          }
        }
        case _ => throw TypeError(t.pos, "expected: sum type, found: " + tType)
      }
    }
    case Inl(t1, t1Type) => t1Type match {
      case TypeSum(sumType1, sumType2) => {
        val realType = typeof(ctx, t1)
        if (realType == sumType1) {
          t1Type
        } else {
          throw TypeError(t.pos, "expected: " + sumType1 + ", found: " + realType)
        }
      }
      case _ => throw TypeError(t.pos, "expected: sum type, found: " + t1Type)
    }
    case Inr(t1, t1Type) => t1Type match {
      case TypeSum(sumType1, sumType2) => {
        val realType = typeof(ctx, t1)
        if (realType == sumType2) {
          t1Type
        } else {
          throw TypeError(t.pos, "expected: " + sumType2 + ", found: " + realType)
        }
      }
      case _ => throw TypeError(t.pos, "expected: sum type, found: " + t1Type)
    }
    case Fix(t1) => {
      val t1Type = typeof(ctx, t1)
      t1Type match {
        case TypeFun(fun1, fun2) => {
          if (fun1 == fun2)
            fun1
          else
            throw TypeError(t.pos, "input and output types should match, found: " + t1Type)
        }
        case _ => throw TypeError(t.pos, "expected: function type, found: " + t1Type)
      }
    }
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
    val tokens = new lexical.Scanner(StreamReader(new java.io.InputStreamReader(System.in)))
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
