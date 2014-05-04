package fos

import scala.collection.mutable.{ Map, HashMap };
import scala.util.parsing.input.Position

case class TypeError(msg: String, pos: Position) extends Exception(msg)

object Type {

  import CT._
  import Utils._

  type Class = String
  type Context = List[Pair[Class, String]]

  def typeOf(tree: Tree, ctx: Context): Class = {
    tree match {
      case Var(name) => ctx find { pair => pair._2 == name } match {
        case Some(Pair(x1, x2)) => x1
        case None => throw new TypeError("Undefined variable " + tree, tree.pos)
      }
      case Select(obj: Expr, field: String) => {
        val objType = typeOf(obj, ctx)
        // get the ClassDef for the found type
        getClassDef(objType, tree.pos).findField(field) match {
          case Some(FieldDef(fldTpe, fldName)) => fldTpe
          case None => throw new TypeError("No field " + field + " for class " + objType, tree.pos)
        }
      }
      case Apply(obj, method, args) => {
        val objType = typeOf(obj, ctx)
        // get the ClassDef for the found type
        getClassDef(objType, tree.pos).findMethod(method) match {
          case Some(x @ MethodDef(_, _, _, _)) => {
            x.checkTypeArguments(args map { typeOf(_, ctx) }, x.pos); x.tpe
          }
          case None => throw new TypeError("No method " + method + " for class " + objType, tree.pos)
        }
      }
      case New(cls, args) => {
        val x = getClassDef(cls, tree.pos)
        x.checkTypeArguments(args map { typeOf(_, ctx) })
        x.name
      }
      case Cast(cls, e) => {
        val x = getClassDef(typeOf(e, ctx), tree.pos)
        if (x.isSubClassOf(cls)) cls
        else if (cls != x.name && x.isSuperclassOf(Option(getClassDef(cls, tree.pos)))) cls
        else {
          println("Stupid Warning: Cast now allowed for expresion " + tree)
          cls
        }
      }
      case tClass @ ClassDef(name, superclass, fields, ctor, methods) => {
        val superClassDef = getClassDef(superclass, tree.pos)

        // check fields
        tClass.checkFields
        
        // check constructor parameters
        tClass.verifyConstructorArgs

        val constrCtx = ctx ::: (tClass.ctor.args map { x: FieldDef => (x.tpe, x.name) }) ::: List((name, "this"))
        // verify that supper is invoked with right types
        val superTypes = ctor.supers map { typeOf(_, constrCtx) }
        superClassDef.checkTypeArguments(superTypes)

        // verify that supper is invoked with right names
        val superNames = ctor.supers map { _.name }
        val superConstrArgNames = superClassDef.ctor.args map { _.name }
        (superNames zip superConstrArgNames) foreach (pair => {
          if (pair._1 != pair._2)
            throw new ClassConstructorArgsException("can't apply " + (superNames).mkString("(", ",", ")") + " to " + 
                superConstrArgNames.mkString("(",",",")") + " for super call", ctor.pos)
        })

        // check other assignments in the constructor body
        ctor.body foreach { assignment =>
          if (assignment.obj != "this") throw new TypeError("Assignment not valid: " + assignment, assignment.pos)

          tClass.findField(assignment.field) match {
            case Some(FieldDef(fldTpe, fldName)) => {
              if (assignment.rhs.name != fldName) throw new TypeError("Expected rhs " + fldName + " in assignment " + assignment, assignment.pos)
            }
            case None => throw new TypeError("Field does not exist: " + assignment, assignment.pos)
          }
        }

        // check methods now 
        methods foreach { method =>
          val methodCtx = ctx ::: (method.args map { x: FieldDef => (x.tpe, x.name) }) ::: List((name, "this"))
          val bodyType = typeOf(method.body, methodCtx)

          // overriding the base method
          tClass.overrideMethod(method.tpe, method.name, method.args, method.body, method.pos)

          // check that E0 <: C0
          getClassDef(bodyType, tree.pos) isSubClassOf getClassDef(method.tpe, tree.pos) match {
            case true => // do nothing
            case false => throw new TypeError("Expected " + method.tpe + ", found " + bodyType, method.body.pos)
          }
        }
        // no exception so far, all good, just return
        ""
      }
      case _ => throw new TypeError("Unexpected form: " + tree, tree.pos)
    }
  }
}

case class EvaluationException(msg: String, pos: Position) extends Exception
case class NoRuleApplies(msg: String, pos: Position) extends Exception

object Evaluate extends (Expr => Expr) {

  import Utils._

  def apply(expr: Expr): Expr = {
    //println("Reduce expr " + expr)
    expr match {
      case x @ Select(obj, field) => obj match {
        case newExpr @ New(cls, args) if !canBeReduced(newExpr) => {
          val newExprClassDef = getClassDef(cls, expr.pos)
          val fields = (newExprClassDef.getFieldsSuperclass ::: newExprClassDef.fields) map { _.name }
          //println("Select no reduce " + expr)
          Evaluate(args(fields.indexOf(field)))
        }
        case _ => Evaluate(Select(Evaluate(obj), field))
      }
      case Apply(obj, method, args) => obj match {
        case newExpr: New if !canBeReduced(newExpr) => {
          // check if we should reduce the arguments
          args collectFirst { case e if canBeReduced(e) => e } match {
            case Some(firstToReduce: Expr) =>
              Evaluate(Apply(obj, method, args collect {
                case e if firstToReduce == e => Evaluate(firstToReduce)
                case e => e
              }))
            case None => {
              // all arguments are reduced, do the substitution
              val methodInfo = getClassDef(newExpr.cls, expr.pos).findMethod(method).get
              val substs = methodInfo.args zip args
              Evaluate(substituteInBody(methodInfo.body, newExpr, substs))
              //println("Apply sub: " + result)
            }
          }
          //println("Apply no reduce for new " + expr)
        }
        case _ => Evaluate(Apply(Evaluate(obj), method, args))
      }
      case Cast(cls, e) => e match {
        case newExpr: New if !canBeReduced(newExpr) => {
          val castClassDef = getClassDef(cls, expr.pos)
          val newClassDef = getClassDef(newExpr.cls, expr.pos)

          if (newClassDef isSubClassOf castClassDef) Evaluate(newExpr)
          else throw new EvaluationException("Cannot cast " + newExpr.cls + " to " + cls + " in expr: " + expr, expr.pos)
        }
        case _ => Evaluate(Cast(cls, Evaluate(e)))
      }
      case newExpr: New => canBeReduced(newExpr) match {
        case true => {
          // find the one to be reduced
          val firstToReduce = newExpr.args collectFirst { case e if canBeReduced(e) => e }

          // keep everything the same, reduce the first one only
          Evaluate(New(newExpr.cls, newExpr.args collect {
            case e if firstToReduce.get == e => Evaluate(e)
            case e: Expr => e
          }))
        }
        case false => newExpr
      }
      case _: Var => expr
      case _ => throw new EvaluationException("Apply: Forgot expression " + expr, expr.pos)
    }
  }

  def canBeReduced(checkExpr: Expr): Boolean = checkExpr match {
    case newExpr: New => newExpr.args collectFirst { case arg if canBeReduced(arg) => arg } match {
      case Some(_) => true
      case None => false
    }
    case _: Select | _: Cast | _: Apply => true
    case _: Var => false
  }

  def substituteInBody(exp: Expr, thiss: New, substs: List[(FieldDef, Expr)]): Expr = exp match {
    case Select(obj: Expr, field: String) => Select(substituteInBody(obj, thiss, substs), field)
    case New(cls, args) => New(cls, args map (arg => substituteInBody(arg, thiss, substs)))
    case Cast(cls, e) => Cast(cls, substituteInBody(e, thiss, substs))
    case Var("this") => thiss
    case Var(bd) => substs find (subs => subs._1.name == bd) match {
      case None => exp
      case Some((_, sub)) => sub
    }

    case Apply(obj, method, args) => Apply(substituteInBody(obj, thiss, substs), method, args map (arg => substituteInBody(arg, thiss, substs)))
    case _ => throw new EvaluationException("Apply: Forgot expression " + exp, exp.pos)
  }
}

object CT {

  val objectClass: String = "Object"
  private val objectClassDef = ClassDef(objectClass, null, Nil, CtrDef(objectClass, Nil, Nil, Nil), Nil)

  private var ct: Map[String, ClassDef] = new HashMap[String, ClassDef]

  add(objectClass, objectClassDef)

  def elements = ct iterator

  def lookup(classname: String): Option[ClassDef] = if (classname != null) ct get classname else None

  // add new entry if already not defined
  def add(key: String, element: ClassDef): Unit = lookup(key) match {
    case Some(x) => throw new TypeError("Duplicate class name: " + key + " is already used", element.pos)
    case None => {

      // check that there is no inheritance cycles
      def checkCycle(start: ClassDef, toCheck: Option[ClassDef]): Boolean = toCheck match {
        case Some(chk: ClassDef) => chk match {
          case _ if chk.name == "Object" => false
          case _ if chk.name == start.name => 
            throw new TypeError("Exception: Inheritance cycle found for class " + start.name, element.pos)
          case _ => checkCycle(start, lookup(chk.superclass))
        }
        case None => false
      }
      
      ct += key -> element
      checkCycle(element, lookup(element.superclass))
    }
  }

  def delete(key: String) = ct -= key

  def printCT: String = ct toString

  def clear(): Unit = {
    ct clear;
    add(objectClass, objectClassDef)
  }

}

object Utils {

  def getClassDef(className: String, pos: Position): ClassDef = CT lookup className match {
    case None => throw new TypeError("class " + className + " not declared", pos)
    case Some(c: ClassDef) => c
  }
}
