package fos

import scala.collection.immutable.{ Set, ListSet }
import scala.util.parsing.input.Position
import scala.util.parsing.input.Positional

abstract class Type {

  override def toString() = this match {
    case TypeVar(a) => a
    case TypeFun(a, b) => "(" + a + " -> " + b + ")"
    case TypeNat => "Nat"
    case TypeBool => "Bool"
  }
}

case class TypeVar(name: String) extends Type
case class TypeFun(type1: Type, type2: Type) extends Type
case object TypeNat extends Type
case object TypeBool extends Type

/** Type Schemes are not types. */
case class TypeScheme(args: List[TypeVar], tp: Type) {
  def instantiate(): Type = {
    val constraints = args map { arg => (arg, Type.freshVariable) } toMap
    val s = new SubstitutionImpl(constraints)
    s(tp)
  }

  override def toString() = args.mkString("[", ", ", "].") + tp
}

object Type {

  type Env = List[(String, TypeScheme)]

  var typeVariableCnt = 0;

  def freshVariable = {
    typeVariableCnt = typeVariableCnt + 1
    TypeVar("T$" + typeVariableCnt)
  }

  def collectTypeVars(t: Type): Set[String] = t match {
    case TypeVar(a) => Set(a)
    case TypeFun(a, b) => collectTypeVars(a) ++ collectTypeVars(b)
    case TypeNat => Set.empty[String]
    case TypeBool => Set.empty[String]
  }

  /** Lookup TypeVar <code>name</code> in the given environment. */
  def lookupTypeVar(env: Env, varName: String): TypeScheme = env match {
    case Nil => null
    case (n, ts) :: env1 => ts.tp match {
      case TypeVar(name) if (varName == name) => ts
      case _ => lookupTypeVar(env1, varName)
    }
  }

  def generalize(tp: Type, env: Env) = {
    val varsToGen = collectTypeVars(tp) filter { (variable) =>
      lookupTypeVar(env, variable) match {
        case ts: TypeScheme => false
        case null => true
      }
    }
    TypeScheme(varsToGen.toList map { name => TypeVar(name) }, tp)
  }
}

abstract class Substitution extends (Type => Type) {

  var indent = 0

  def apply(tp: Type): Type = {
    //println("  " * indent + "in: " + tp + "   subst: " + this)
    indent = indent + 1
    val result = tp match {
      case TypeNat => TypeNat
      case TypeBool => TypeBool
      case TypeFun(t1, t2) => TypeFun(this(t1), this(t2))
      case v: TypeVar => inDomain(v) match {
        case Some(t) => t
        case None => v
      }
      case _ => null
    }
    indent = indent - 1
    //println("  " * indent + "out: " + result + "   subst: " + this)
    result
  }
  override def toString() = ""

  def apply(p: (Type, Type)): (Type, Type) = p match {
    case Pair(t1, t2) => (this(t1), this(t2))
  }

  def apply(env: List[(String, TypeScheme)]): List[(String, TypeScheme)] =
    env map { (pair) => (pair._1, TypeScheme(pair._2.args, apply(pair._2.tp))) }
  /*
  def apply(constr: List[(Type, Type)]): List[(Type, Type)] = {
    constr map { (pair) => apply(pair) }
  }
*/
  def compose(s: Substitution): Substitution

  def extend(cKey: TypeVar, cVal:Type): Substitution

  def constraints(): Map[TypeVar, Type]

  def inDomain(t: TypeVar): Option[Type] = {
    constraints.contains(t) match {
      case true => Some(constraints()(t))
      case false => None
    }
  }
}

/** The empty substitution. */
object emptySubst extends Substitution {
  def lookup(t: TypeVar) = t
  def constraints() = Map.empty[TypeVar, Type]
  def compose(s: Substitution): Substitution = s
  def extend(cKey: TypeVar, cVal:Type): Substitution = new SubstitutionImpl(Map(cKey->cVal))
}

class SubstitutionImpl(cMap: Map[TypeVar, Type]) extends Substitution {
  def constraints() = cMap

  def compose(s: Substitution) = {
    var c = s.constraints collect { case (key, value) => (key -> this(value)) }
    c = c ++ (this.constraints filter { case (key, value) =>
      s.inDomain(key) match {
        case Some(_) => false
        case None => true
      }
    })
    new SubstitutionImpl(c)
  }

  def extend(cKey: TypeVar, cVal: Type):Substitution = this.compose(new SubstitutionImpl(Map(cKey -> cVal)))
}
