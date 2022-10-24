/**
 * FunLang to SEC translator.
 *
 * Copyright 2022, Anthony Sloane, Kym Haines, Macquarie University, All rights reserved.
 */

package funlang

/**
 * Translator from FunLang source programs to SEC target programs.
 */
object Translator {

    import SECTree._
    import FunLangTree._
    import scala.collection.mutable.ListBuffer

    /**
     * Return a frame that represents the SEC instructions for a FunLang program.
     */
    def translate (program : Program) : Frame = {

        // An instruction buffer for accumulating the program instructions
        val programInstrBuffer = new ListBuffer[Instr] ()

        /**
         * Translate the program by translating its expression.
         */
        val expInstrs = translateExpression (program.exp)
        programInstrBuffer.appendAll (expInstrs)
        programInstrBuffer.append (IPrint ())

        // Gather the program's instructions and return them
        programInstrBuffer.result ()

    }

    /**
     * Translate an expression and return a list of the instructions that
     * form the translation.
     */
    def translateExpression (exp : Exp) : Frame = {

        // An instruction buffer for accumulating the expression instructions
        val expInstrBuffer = new ListBuffer[Instr] ()

        /**
         * Generate an instruction by appending it to the instruction buffer.
         */
        def gen (instr : Instr) {
            expInstrBuffer.append (instr)
        }

        /**
         * Generate a sequence of instructions by appending them all to the
         * instruction buffer.
         */
        def genall (frame : Frame) {
            expInstrBuffer.appendAll (frame)
        }

        /**
         * Generate code to make a closure (argName => body).
         */
        def genMkClosure (argName : String, body : Exp) {
            val bodyInstrs = translateExpression (body)
            gen (IClosure (argName, bodyInstrs :+ IPopEnv ()))
        }

       /**
        *  AppExp helper functions
        */
        
        /* Used to generate IHead, ITail and ILength instructions */
        def appExpHelper(instr: Instr, argExp: Exp) = {
            genall(translateExpression(argExp))
            gen(instr)
        }

        /* Used to apply IHead, ITail and ILength instructions to a list */
        def listOperation(name:String, list:Exp):Exp = {
            AppExp(IdnUse(name), list)
        }

       /**
        *   BlockExp helper functions
        */

        def translateMultipleDefns(defns: Vector[Defn], exp: Exp):Exp = {
            defns match {
                case h +: t => translateDefn(h, translateMultipleDefns(t, exp))
                case _ => exp
            }
        }

        def translateDefn(defn: Defn, body: Exp):Exp = {
            defn match {
                case Defn(idndef, exp) => AppExp(LamExp(idndef, body), exp)
            }
        }

       /**
        *   MatchExp helper functions
        */

        def translateCases(cases: Vector[(Pat, Exp)], matchExp: Exp):Exp = {
            cases match {
                case h +: t => translateCase(h, IdnUse("x"), translateCases(t, matchExp))
                case _ => IntExp(999)
            }
        }

        def translateCase(c: (Pat, Exp), matchExp: Exp, elseExp: Exp):Exp = {
            c match {
                case (LiteralPat(patExp), thenExp) => IfExp(EqualExp(matchExp, patExp), thenExp, elseExp)
                case (IdentPat(patString), exp) => AppExp(LamExp(IdnDef(patString, UnknownType()), exp), matchExp)
                case (ConsPat(leftPat, rightPat), thenExp) => translateListPat(Vector(leftPat, rightPat), matchExp, thenExp, elseExp)
                case (ListPat(pats), thenExp) => translateListPat(pats, matchExp, thenExp, elseExp)
                case (AnyPat(), exp) => exp
                case _ => IntExp(999)
            }
        }
        
       /**
        *   Helper functions that deal with matching ListPats
        */

        def translateListPat(pats:Vector[Pat], matchExp:Exp, thenExp:Exp, elseExp:Exp):Exp = {
            IfExp(EqualExp(checkListLength(pats, matchExp), BoolExp(true)), listThenExp(pats, thenExp, matchExp), elseExp)
        }

        def listThenExp(pats:Vector[Pat], thenExp:Exp, matchExp:Exp):Exp = {
            pats match {
                case h +: t => AppExp(LamExp(IdnDef(getIdentPat(h), UnknownType()), listThenExp(t, thenExp, listOperation("tail", matchExp))), listOperation("head", matchExp))
                case _ => thenExp
            }
        }

        def getIdentPat(pat:Pat):String = {
            pat match {
                case IdentPat(string) => string
                case _ => ""
            }
        }

        def checkListLength(pats:Vector[Pat], matchExp:Exp) = {
            IfExp(EqualExp(listOperation("length", matchExp), IntExp(0)), BoolExp(false), translateListPats(pats, matchExp))
        }

        def translateListPats(pats:Vector[Pat], matchExp:Exp):Exp = {
            pats match {
                case pat +: t => IfExp(EqualExp(checkListPat(pat, matchExp), BoolExp(true)), 
                                        translateListPats(t, listOperation("tail", matchExp)), BoolExp(false))
                case _ => BoolExp(true)
            }
        }

        def checkListPat(pat:Pat, matchExp:Exp):Exp = {
            pat match {
                case LiteralPat(exp) => IfExp(EqualExp(listOperation("head", matchExp), exp), BoolExp(true), BoolExp(false))
                case IdentPat(_) => BoolExp(true)
                case AnyPat() => BoolExp(true)
                case _ => BoolExp(false)
            }
        }

      /**
        *   Helper functions that deal with matching ConPats
        */
        def translateConPat(leftPat:Pat, rightPat:Pat, matchExp:Exp, thenExp:Exp, elseExp:Exp):Exp = {
            IfExp(EqualExp(checkListLengthCon(leftPat, matchExp), BoolExp(true)), consThenExp(Vector(leftPat, rightPat), thenExp, matchExp), elseExp)
        }

        def consThenExp(pats:Vector[Pat], thenExp:Exp, matchExp:Exp):Exp = {
            pats match {
                case h +: t => AppExp(LamExp(IdnDef(getIdentPat(h), UnknownType()), listThenExp(t, thenExp, listOperation("tail", matchExp))), listOperation("head", matchExp))
                case _ => thenExp
            }
        }

        def checkListLengthCon(leftPat:Pat, matchExp:Exp):Exp = {
            IfExp(EqualExp(listOperation("length", matchExp), IntExp(0)), BoolExp(false), checkConsPat(leftPat, matchExp))
        }

        def checkConsPat(leftPat:Pat, matchExp:Exp):Exp = {
            leftPat match {
                case LiteralPat(exp) => IfExp(EqualExp(listOperation("head", matchExp), exp), BoolExp(true), BoolExp(false))
                case IdentPat(_) => BoolExp(true)
                case AnyPat() => BoolExp(true)
                case _ => BoolExp(false)
            }
        }

      /**
        *   End of helper functions
        */

        exp match {

        case IdnUse (value) =>
            gen (IVar (value))

        case IntExp (value) =>
            gen (IInt (value))

        case BoolExp (value) =>
            gen (IBool (value))

        case PlusExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IAdd ())

        case MinusExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ISub ())

        case SlashExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IDiv ())

        case StarExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IMul ())

        case LessExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ILess ())

        case EqualExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IEqual ())

        case LamExp (IdnDef (name, _), body) =>
            genMkClosure(name, body)

        case ConsExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ICons ())

        case ListExp (exps) => 
            exps.foreach(exp => genall(translateExpression(exp)))
            gen(INil())
            (0 until exps.length).foreach(x => gen(ICons()))

        case IfExp (condExp, thenExp, elseExp) => 
            genall(translateExpression(condExp))
            gen(IBranch(translateExpression(thenExp), translateExpression(elseExp)))

        case AppExp (funExp, argExp) => 
            funExp match {
                case IdnUse(r) if(r == "head")   => appExpHelper(IHead(), argExp)
                case IdnUse(r) if(r == "tail")   => appExpHelper(ITail(), argExp)
                case IdnUse(r) if(r == "length") => appExpHelper(ILength(), argExp)
                case _                           => {
                    genall(translateExpression(funExp))
                    genall(translateExpression(argExp))
                    gen(ICall())
                }
            }

        case BlockExp (defns, exp) =>
            genall(translateExpression(translateMultipleDefns(defns, exp)))
        
        case MatchExp(exp, cases) => 
            genall(translateExpression(AppExp(LamExp(IdnDef("x", UnknownType()), translateCases(cases, exp)), exp)))



        // FIXME
        // handle:
        //    IfExp
        //    AppExp - "head" (exp)
        //           - "tail" (exp)
        //           - "length" (exp)
        //           - all other: exp (exp)
        //    ListExp
        //    BlockExp
        //    MatchExp

        case _ =>
            gen (IPrint ())
        }

        // Gather the expression's instructions and return them
        expInstrBuffer.result ()

    }
}
