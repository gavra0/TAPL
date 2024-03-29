package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

import java.io.PrintWriter
import scala.collection.immutable.{Map,ListMap}

import CT._
import Utils._

abstract class TreeException(msg: String, pos: Position) extends Exception

abstract class ClassException(msg: String, pos: Position) extends TreeException(msg, pos)
case class ClassConstructorArgsException(msg: String, pos: Position) extends ClassException(msg, pos)

abstract class MethodException(msg: String, pos: Position) extends TreeException(msg, pos)
case class MethodArgsException(msg: String, pos: Position) extends MethodException(msg, pos)
case class MethodOverrideException(msg: String, pos: Position) extends MethodException(msg, pos)
case class MethodArgsLengthException(msg: String, pos: Position) extends MethodException(msg, pos)

abstract class FieldException(msg: String, pos: Position) extends TreeException(msg, pos)
case class FieldAlreadyDefined(msg: String, pos: Position) extends FieldException(msg, pos)


sealed abstract class Tree extends Positional

case class Program(cls: List[ClassDef], expr: Expr) extends Tree {
  cls.foreach(c => CT.add(c.name,c));
}
case class ClassDef(name: String, superclass: String, fields: List[FieldDef], ctor: CtrDef, methods: List[MethodDef]) extends Tree {
  private def fieldLookup: List[FieldDef] = {
    CT lookup superclass match {
      case None => fields
      case Some(s) => s.fieldLookup ::: fields
    }
  }

  def getFieldsSuperclass: List[FieldDef] = getClassDef(superclass, pos) fieldLookup

  def findField(fieldName: String): Option[FieldDef] = fieldLookup find (f => f.name == fieldName)

  def checkFields: Unit = checkListFieldsDef(fieldLookup)

  /**
   * Verify that in the list there is no two occurrence of the same variable name
   * Should throw FieldAlreadyDefined exception.
   */
  private def checkListFieldsDef(f: List[FieldDef]): Unit = {
    f find (field => (f count (_field => _field.name == field.name)) > 1) match {
      case None => ()
      case Some(varfield) => throw FieldAlreadyDefined("variable "+varfield.name+" is already defined in the scope", varfield.pos)
    }
  }

  def findMethod(methodName: String): Option[MethodDef] = methods find (m => m.name == methodName) match {
    case None => CT lookup superclass match {
      case None => None
      case Some(superc) => superc findMethod methodName
    }
    case Some(method) => Some(method)
  }

  def overrideMethod(tpe: String, name: String, args: List[FieldDef], body: Expr, poss: Position): Unit = {
    if( (methods count (m => m.name == name)) > 1) throw new MethodOverrideException("In class " + this.name + ", method "+name+" is defined more than once", poss)
    try {
      checkListFieldsDef(args);
    } catch {
      case FieldAlreadyDefined(msg, pos) => throw FieldAlreadyDefined("In class "+this.name+", in the arguments of method "+name+", "+msg, pos)
    }
    val inheritedMethod = getClassDef(superclass, pos) findMethod(name);
    inheritedMethod match {
      case None => ()
      case Some(MethodDef(tpeS,_,argsS, _)) =>
        var error = false;
        if(tpe == tpeS) {
          val paramsOvMethod = args map (arg => arg.tpe);
          val paramsInMethod = argsS map (argS => argS.tpe);
          if(args.length != argsS.length)
            throw new MethodOverrideException("can't apply "+paramsOvMethod.mkString ("(",",",")")+" to "+paramsInMethod.mkString ("(",",",")"), poss)
          for (i <- List.range(0,paramsInMethod length)) {
            if( (paramsInMethod(i) != paramsOvMethod(i)) && !error) error = true;
          }
          if(error)
            throw new MethodOverrideException("can't apply "+paramsOvMethod .mkString ("(",",",")")+" to "+paramsInMethod.mkString ("(",",",")"), poss)
          () //Everything was ok, so override ok
        } else
          throw new MethodOverrideException("Type mismatch. The return type "+tpeS+" of inherithed "+
            "method "+name+" has different signature. Overriding method has type "+tpe, poss)
    }
  }
 /**
  * checkTypeArguments: verify only the type of the parameters not the name
  * Should throw ClassConstructorArgsException's.
  */
  def checkTypeArguments(argsType: List[String]): Unit =  {
    var errorSub = Pair(false,0);
    val typeFields: List[String] = fieldLookup map (fd => fd.tpe);
    if( (typeFields length) == (argsType length)) {
      for (i <- List.range(0,typeFields length)) {
        if( !( getClassDef(argsType(i), pos).isSubClassOf(typeFields(i)) ) && !errorSub._1) errorSub = Pair(true,i);
      }
      if(errorSub._1)
        throw new ClassConstructorArgsException("can't apply "+argsType .mkString ("(",",",")")+" to "+typeFields.mkString ("(",",",")")+" because "+
          argsType(errorSub._2)+" is not a subtype of "+typeFields(errorSub._2), ctor.pos)
      () //no errors means everything was fine
    } else
      throw new ClassConstructorArgsException("can't apply "+argsType .mkString ("(",",",")")+" to "+typeFields .mkString ("(",",",")"), ctor.pos)
  }

  /**
   * verifyConstructorArgs: verify the name and the type of each parameter in the constructor respect to the fields declared in the class.
   * Should throw FieldAlreadyDefined and ClassConstructorArgsException.
   */
  def verifyConstructorArgs: Unit = {
     try {
       checkListFieldsDef (ctor.args);
     } catch {
       case FieldAlreadyDefined(msg, pos) => throw FieldAlreadyDefined("In class " + name + ", in the constructor, "+msg, pos)
     }
    val fieldss = fieldLookup;
    val fieldsType = fieldss map (fd => fd.tpe);
    val constructType = ctor.args map (arg => arg.tpe);
    if (fieldss.length != (ctor.args length) )
      throw new ClassConstructorArgsException("can't apply "+constructType.mkString ("(",",",")")+
        " to "+fieldsType.mkString ("(",",",")"), ctor.pos)
    (fieldss zip ctor.args) foreach ( pair => {
      if(pair._1 != pair._2)
        throw new ClassConstructorArgsException("can't apply "+(ctor.args).mkString ("(",",",")")+
          " to "+fieldss.mkString ("(",",",")"), ctor.pos)
    })
    () //No error means every parameter of the constructor has the same type and name of the ones in the class
  }


  def superClass: Option[ClassDef] = CT lookup (this superclass)

  def isSuperclassOf(that: Option[ClassDef]): Boolean =
    that match {
    case None => false
    case Some(sub) =>
      //C <: C
      if(name == sub.name) true
      else {
        // CT(C) = class C extends D {...} -> C <: D OR C <: D & D <: E -> C <: E
        this isSuperclassOf (sub superClass)
    }
  }

  def isSubClassOf(that: ClassDef): Boolean = that isSuperclassOf Some(this)

  def isSubClassOf(that: String) : Boolean = isSubClassOf (getClassDef(that, pos))
}

case class FieldDef(tpe: String, name: String) extends Tree {
  override def toString = tpe+" "+name
}

case class CtrDef(name: String, args: List[FieldDef], supers: List[Var], body: List[Assign]) extends Tree

case class Assign(obj: String, field: String, rhs: Var) extends Tree

case class MethodDef(tpe: String, name: String, args: List[FieldDef], body: Expr) extends Tree {

  /*
   * Check type arguments of method definiton. Should throw MethodArgsException's.
   */
  def checkTypeArguments(argsType: List[String], pos: Position): Unit =  {
      var error = false;
      val params = (args map (arg => arg.tpe));
      if( (params length) == (argsType length)) {
        for (i <- List.range(0,params length)) {
          if( !((getClassDef(argsType(i), pos)) isSubClassOf params(i)) && !error) error = true;
        }
        if(error)
          throw new MethodArgsException("can't apply "+argsType.mkString ("(",",",")")+" to "+params.mkString ("(",",",")"), pos)
        ()
      } else
        throw new MethodArgsException("can't apply "+argsType.mkString ("(",",",")")+" to "+params.mkString ("(",",",")"), pos)
  }
}

abstract class Expr extends Tree

case class Var(name: String) extends Expr {
  override def toString = name
}
case class New(cls: String, args: List[Expr]) extends Expr {
  override def toString = "new "+cls+""+args.mkString("(",",",")")
}
case class Cast(cls: String, e: Expr) extends Expr {
  override def toString = "( ("+cls+")"+e+")"
}
case class Select(obj: Expr, field: String) extends Expr {
  override def toString = obj+"."+field
}
case class Apply(obj: Expr, method: String, args: List[Expr]) extends Expr {
  override def toString = obj+"."+method+""+args.mkString("(",",",")")
}


/**
 * Pretty printer using scala.text formatting library. It works
 * by first building a document abstracting over nesting, spacing and
 * new lines, and afterwards rendering the text given a Writer and a
 * desired width.
 */
object PrettyPrinter  {
  def apply(t: Tree) = {
    val writer = new PrintWriter(System.out)
    toDocument(t).format(80, writer)
    writer.println
    writer.flush()
  }

  import scala.text._
  import scala.text.Document._

  def toDocument(ts: List[Tree], sep: String, suffix: String): Document = ts match {
    case one :: two :: rest =>
      toDocument(one) :: sep :/: rest.foldLeft(toDocument(two))  { (d, e) =>
        if (sep != "") d :: sep :/: toDocument(e)
        else d :/: toDocument(e) } :: text(suffix)
    case one :: Nil =>
      toDocument(one) :: text(suffix)
    case Nil =>
      empty
  }

  def toDocument(t: Tree): Document = t match {
    case Program(cls, expr) =>
      group(toDocument(cls, "", "")) :/: group(toDocument(expr))

    case ClassDef(name, superclass, fields, ctor, methods) =>
      group("class " :: name :/: "extends " :: superclass :: empty) ::
         nest(2, " {" :/: group(toDocument(fields, ";", ";") :/: toDocument(ctor) :/: toDocument(methods, "", ""))) :/:
      "}" :/: empty

    case FieldDef(tpe, name) =>
      group(tpe :/: text(name))

    case CtrDef(name, args, supers, body) =>
      group(name :: "(" :: group(toDocument(args, ",", "")) :: ")" :: empty) :/:
        nest(2,  "{" :/:
            group("super(" :: group(toDocument(supers, ",", "")) :: ");" :/: empty) :/:
            group(toDocument(body, "", ""))
            ) :/:
      "}" :/: empty

    case Assign(obj, field, rhs) =>
      group(obj :: "." :: field :/: "=" :/: toDocument(rhs) :: ";" :/: empty)

    case MethodDef(tpe, name, args, body) =>
      group(tpe :/: name :/: "(" :: group(toDocument(args, ",", "")) :: ")" :/: text("{")) :/:
        nest(2, "return " :: group(toDocument(body))) :/:
      "}" :/: empty

    case Var(name) =>
      text(name)

    case New(cls, args) =>
      "new " :: cls :: "(" :: group(toDocument(args, ",", "") :: text(")"))
    case Cast(cls, expr) =>
      group("(" :: cls :: ")" :/: toDocument(expr))

    case Select(obj, field) =>
      toDocument(obj) :: "." :: text(field)

    case Apply(obj, meth, args) =>
      toDocument(obj) :: "." :: meth :: nest(2, "(" :: group(toDocument(args, ",", "")) :: text(")"))

    case _ =>
      super.toString :/: empty
  }
}
