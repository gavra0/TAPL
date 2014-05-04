package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.StreamReader

/**
 * This object implements a parser and evaluator for the NB
 * language of booleans and numbers found in Chapter 3 of
 * the TAPL book.
 */
object NBLanguage extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")

  /**
   * Expr ::= 'true'
   * | 'false'
   * | 'if' Expr 'then' Expr 'else' Expr
   * | '0'
   * | 'succ' Expr
   * | 'pred' Expr
   * | 'iszero' Expr
   */
  def Expr: Parser[Term] = (
    "true" ^^^ BoolValue(true)
      | "false" ^^^ BoolValue(false)
      | "if" ~ Expr ~ "then" ~ Expr ~ "else" ~ Expr ^^ {
      case "if" ~ e1 ~ "then" ~ e2 ~ "else" ~ e3 => IfThenElse(e1, e2, e3)
    }
      | (nv | "succ" ~> Expr ^^ {
      case e1 => Succ(e1)
    })
      | "pred" ~> Expr ^^ {
      case e1 => Pred(e1)
    }
      | "iszero" ~> Expr ^^ {
      case e1 => IsZero(e1)
    }
      | failure("illegal start of expression")
    )

  /**
   * NV ::= numericLit | succ NV
   * We allow numeric values greater than 0 as well in this parser
   * @return parsed term
   */
  def nv: Parser[Term] =
    rep("succ") ~ numericLit ^^ {
      case list ~ numLit => syntacticSugar(list.size + numLit.toInt)
    }

  /**
   * Decompose the numeric values to succs succ(succ(succ...(0)..))
   * @param x value read by parser, can be any value greater or equal to 0
   * @return either [[fos.ZeroValue]] or [[fos.Succ]] term
   */
  def syntacticSugar(x: Int): Term = {
    if (x == 0) {
      ZeroValue()
    } else {
      Succ(syntacticSugar(x - 1))
    }
  }

  /**
   * Computation and congruence rules applied
   * @param node AST that is meant to be reduced
   * @return reduced AST or stuck term
   */
  def reduceGrammar(node: Term): Term = {
    node match {
      case IfThenElse(e1, e2, e3) => {
        if (e1.isInstanceOf[BoolValue]) {
          if ((e1.asInstanceOf[BoolValue]).x) {
            e2
          } else {
            e3
          }
        } else {
          IfThenElse(reduceGrammar(e1), e2, e3)
        }
      }
      case IsZero(e1) => {
        e1 match {
          case ZeroValue() => BoolValue(true)
          case Succ(e2) => {
            if (e1.asInstanceOf[Succ].isNumeric) {
              BoolValue(false)
            } else {
              IsZero(Succ(reduceGrammar(e2)))
            }
          }
          case _ => IsZero(reduceGrammar(e1))
        }
      }
      case Pred(e1) => {
        e1 match {
          case ZeroValue() => e1
          case Succ(e2) => {
            if (e1.asInstanceOf[Succ].isNumeric) {
              e2
            } else {
              Pred(Succ(reduceGrammar(e2)))
            }
          }
          case _ => Pred(reduceGrammar(e1))
        }
      }
      case Succ(e1) => {
        e1 match {
          case ZeroValue() => node
          case Succ(e2) => {
            if (e1.asInstanceOf[Succ].isNumeric) {
              node
            } else {
              Succ(Succ(reduceGrammar(e2)))
            }
          }
          case _ => {
            Succ(reduceGrammar(e1))
          }
        }
      }
      case _ => node
    }
  }

  /**
   * Big step semantics applied to the term
   * @param node AST that we want to reduce
   * @return reduced AST or stuck term
   */
  def bigStepReduce(node: Term): Term = {
    node match {
      //ovo pokriva case _ => node
      case BoolValue(e1) => node
      case ZeroValue() => node
      case Succ(e1) => {
        val e1Reduced = bigStepReduce(e1)
        if (isNumericValue(e1Reduced)) {
          Succ(e1Reduced)
        } else {
          checkStuckTerm(e1Reduced, node)
        }
      }
      case IfThenElse(e1, e2, e3) => {
        val e1Reduced = bigStepReduce(e1)
        if (e1Reduced.isInstanceOf[BoolValue]) {
          if ((e1Reduced.asInstanceOf[BoolValue]).x) {
            bigStepReduce(e2)
          } else {
            bigStepReduce(e3)
          }
        } else {
          checkStuckTerm(e1Reduced, node)
        }
      }
      case Pred(e1) => {
        val e1Reduced = bigStepReduce(e1)
        if (e1Reduced.isInstanceOf[ZeroValue]) {
          e1Reduced
        } else if (isNumericValue(e1Reduced)) {
          e1Reduced.asInstanceOf[Succ].t
        } else {
          checkStuckTerm(e1Reduced, node)
        }
      }
      case IsZero(e1) => {
        val e1Reduced = bigStepReduce(e1)
        if (e1Reduced.isInstanceOf[ZeroValue]) {
          BoolValue(true)
        } else if (isNumericValue(e1Reduced)) {
          BoolValue(false)
        } else {
          checkStuckTerm(e1Reduced, node)
        }
      }
      case _ => node
    }
  }

  /**
   * Check if succ succ succ..0 or just 0
   */
  def isNumericValue(t: Term): Boolean = {
    t.isInstanceOf[ZeroValue] || (t.isInstanceOf[Succ] && t.asInstanceOf[Succ].isNumeric())
  }

  /**
   * Check if the result valid
   * @param t
   * @return
   */
  def validResult(t: Term): Boolean = {
    isNumericValue(t) || t.isInstanceOf[BoolValue]
  }

  /**
   * Checks if the stuck term is valid result, in which case it could not be reduced because of the surrounding term
   * and in that case the node is returned
   * @param term "inside" term
   * @param node term "surrounding" the term
   * @return the smallest part of the AST that could not be reduced
   */
  def checkStuckTerm(term: Term, node: Term): Term = {
    if (validResult(term)) {
      node
    } else {
      term
    }
  }

  def main(args: Array[String]): Unit = {
    /*val inputs = Array("iszero 0", "if iszero 0 then true else false", "iszero pred succ 0", "", "if pred succ succ 0 then if iszero 0 then true else false else succ succ succ succ 0",
    "if if true then iszero pred succ succ 0 else pred 0 then iszero pred succ pred succ 0 else if pred succ succ pred succ 0 then true else false")*/

    val tokens = new lexical.Scanner(StreamReader(new java.io.InputStreamReader(System.in)))
    phrase(Expr)(tokens) match {
      case Success(tree, _) => {
        var oldTree: Term = null
        var newTree = tree
        print("\n")
        while (oldTree != newTree) {
          println(newTree)
          oldTree = newTree
          newTree = reduceGrammar(oldTree)
        }

        if (!validResult(newTree)) {
          println("Stuck term: " + newTree)
        }

        print("Big step: ")
        val bigStepResultTree = bigStepReduce(tree)
        if (!validResult(bigStepResultTree)) {
          print("Stuck term: ")
        }
        println(bigStepResultTree)
      }
      case err => {
        println(err)
      }
    }
  }
}
