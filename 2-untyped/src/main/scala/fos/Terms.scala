package fos

import scala.util.parsing.input.Positional

/** Abstract Syntax Trees for terms. */
abstract class Term(val hasParenthesis:Boolean) extends Positional {
  
  def copyAndSetParen(hasParen: Boolean = true): Term = this match {
    case Variable(x) => Variable(x)
    case Abstraction(x, t, _) => Abstraction(x, t, hasParen)
    case Application(t1, t2, _) => Application(t1, t2, hasParen)
  }
  
  def printParenthesis(s: String): String = {
    if(hasParenthesis) {
      "(" + s + ")"
    } else {
      s
    }
  }
  
  def fv(): Set[String] = this match {
    case Variable(n) => Set(n)
    case Abstraction(v, b, _) => b.fv - v.name
    case Application(t1, t2, _) => t1.fv union t2.fv
    case _ => Set()
  }
  
  def isValue(): Boolean = this match {
    case Abstraction(_, _, _) => true
    case _ => false
  }
}

object Term {
  var keepParenthesis = true
}

abstract class AbsVar(hasParenthesis: Boolean) extends Term(hasParenthesis: Boolean)

case class Variable(name: String) extends AbsVar(false) { // no need for parenthesis here  
  override def toString(): String = {
    name
  }
}

case class Abstraction(x:Variable, t:Term, hasParen: Boolean = false) extends AbsVar(hasParen: Boolean) {  
  override def toString():String = {
    printParenthesis("\\" + x + "."  + t)
  }
}

case class Application(var t1: Term, t2: Term, hasParen: Boolean = false) extends Term(hasParen: Boolean) {
  
  {
    if(t1.hasParenthesis && (!t1.isInstanceOf[Abstraction]) && !Term.keepParenthesis) {
      t1 = t1.copyAndSetParen(false)
    }
  }
  
  override def toString():String = {
    printParenthesis(t1 + " " + t2)
  }
}