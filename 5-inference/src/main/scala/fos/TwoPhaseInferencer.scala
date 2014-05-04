package fos

import scala.util.parsing.input.Positional
import scala.util.parsing.input.Position
import scala.util.parsing.input.NoPosition

/** Two-phase inferencer, first collect constraints, then solve them. */
class TwoPhaseInferencer extends TypeInferencers {
  import Type._

  class Constraint(val c: (Type, Type), p: Position) extends Positional {
    setPos(p)
  }
  
  val noConstraints: List[Constraint] = Nil
  case class TypingResult(tpe: Type, c: List[Constraint])

  /**
   * Type <code>t</code> in <code>env</code> and return its type and a
   *  constraint list.
   */
  def collect(env: Env, t: Term): TypingResult = t match {
    case True => TypingResult(TypeBool, noConstraints)
    case False => TypingResult(TypeBool, noConstraints)
    case Zero => TypingResult(TypeNat, noConstraints)
    case Pred(t1) => {
      val t1tr = collect(env, t1)
      TypingResult(TypeNat, t1tr.c :+ new Constraint((t1tr.tpe, TypeNat), t1.pos))
    }
    case Succ(t1) => {
      val t1tr = collect(env, t1)
      TypingResult(TypeNat, t1tr.c :+ new Constraint((t1tr.tpe, TypeNat), t1.pos))
    }
    case IsZero(t1) => {
      val t1tr = collect(env, t1)
      TypingResult(TypeBool, t1tr.c :+ new Constraint((t1tr.tpe, TypeNat), t1.pos))
    }
    case If(cond, t1, t2) => {
      val condtr = collect(env, cond)
      val t1tr = collect(env, t1)
      val t2tr = collect(env, t2)

      val condConstr = new Constraint((condtr.tpe, TypeBool), cond.pos)
      val t1t2Constr = new Constraint((t1tr.tpe, t2tr.tpe), t.pos)

      TypingResult(t1tr.tpe, condtr.c ++ t1tr.c ++ t2tr.c :+ condConstr :+ t1t2Constr)
    }
    case Var(x) => {
      val t1 = lookup(env, x)
      if (t1 == null)
        throw TypeError("Unknown variable " + x, t.pos)
      TypingResult(t1.instantiate, noConstraints)
    }
    case Abs(v, tp, t1) => {      
      //TypeScheme has empty args list in order to avoid incorrect instantiation of abstraction parameter
      val vTypeSchema =  tp match {
	    case EmptyType => {
	      val freshVar = freshVariable
	      TypeScheme(Nil, freshVar)
	    }
	    case _ => TypeScheme(Nil, toType(tp))
	  }
      val t1tr = collect((v, vTypeSchema) +: env, t1)
      TypingResult(TypeFun(vTypeSchema.tp, t1tr.tpe), t1tr.c)
    }
    case App(t1, t2) => {
      val t1tr = collect(env, t1)
      val t2tr = collect(env, t2)
      val freshVar = freshVariable
      val pos = if(t1.pos == NoPosition) t.pos else t1.pos //sometimes t.pos = NoPosition, while sometimes t1.pos = NoPosition
      val appConstr = new Constraint((t1tr.tpe, TypeFun(t2tr.tpe, freshVar)), pos)

      TypingResult(freshVar, t1tr.c ++ t2tr.c :+ appConstr)
    }
    case Let(x, xtp, v, t1) => {
      var vtr = collect(env, v) 
      vtr = xtp match {
        case EmptyType => vtr
        case _ => {
          val xtpType = toType(xtp)
          TypingResult(xtpType, vtr.c :+ new Constraint ((vtr.tpe, xtpType), v.pos))
        }
      }
      val s = unify(vtr.c)
      val svtp = s(vtr.tpe)
      var newEnv = s(env)
      newEnv = newEnv :+ (x, generalize(svtp, newEnv))
      
      collect(newEnv, t1)
    }
  }

  def unify(c: List[Constraint]): Substitution =
    if (c.isEmpty) emptySubst
    else c.head.c match {
      case (TypeVar(a), TypeVar(b)) if (a == b) => unify(c.tail)
      case (TypeBool, TypeBool) => unify(c.tail)
      case (TypeNat, TypeNat) => unify(c.tail)
      case (tVar@TypeVar(a), b) if (!(collectTypeVars(b) contains a)) => {
        val s = new SubstitutionImpl(Map(tVar -> b))
        unify(c.tail map { (constr) => new Constraint(s(constr.c), constr.pos) }).compose(s)
      }
      case (a, tVar@TypeVar(b)) if (!(collectTypeVars(a) contains b)) => {
        val s = new SubstitutionImpl(Map(tVar->a))
        unify(c.tail map { (constr) => new Constraint(s(constr.c), constr.pos) }).compose(s)
      }
      case (TypeFun(s1,s2), TypeFun(t1,t2)) => {
        unify(c.tail :+ new Constraint((s1, t1), c.head.pos) :+ new Constraint((s2, t2), c.head.pos))
      }
      case (t1, t2) => throw TypeError("Could not unify: " + t1 + " with " + t2, c.head.pos)
    }

  override def typeOf(t: Term): Type = try {
    val TypingResult(tp, c) = collect(Nil: Env, t)
    val s = unify(c)
    s(tp)
  } catch {
    case TypeError(msg, pos) =>{
      Console.println("type error: " + msg)
      Console.println(pos.longString)
      null
    }
  }

}
