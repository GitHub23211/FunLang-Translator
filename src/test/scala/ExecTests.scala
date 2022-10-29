/**
 * FunLang language execution tests.
 *
 * Copyright 2022, Anthony Sloane, Kym Haines, Macquarie University, All rights reserved.
 */

package funlang

import org.bitbucket.inkytonik.kiama.util.ParseTests
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

/**
 * Tests that check that the translation works correctly.
 */
@RunWith(classOf[JUnitRunner])
class ExecTests extends ParseTests {

    import org.bitbucket.inkytonik.kiama.util.StringSource
    import org.bitbucket.inkytonik.kiama.util.StringEmitter
    import org.bitbucket.inkytonik.kiama.parsing.{Success,Failure,Error}

    import FunLangTree._
    import SECTree._

    val parsers = new SyntaxAnalysis (positions)
    import parsers._

    /**
     * Parse some test input and, if the parse succeeds with no input left,
     * return the program tree. If the parse fails, fail the test.
     */
    def parseProgram (str : String) : Program = {
        val posns = positions

        // Create a messaging module for semantic analysis
        /*
        val messaging = new Messaging with PositionStore {
                           override val positions = posns
                        }
        */

        parseAll (program, new StringSource(str)) match {
            case Success (r, in) =>
                if (!in.atEnd) fail ("input remaining at " + in.pos)
                r
            case f : Error =>
                fail ("parse error: " + f)
            case f : Failure =>
                fail ("parse failure: " + f)
        }
    }

    /**
     * Parse some test input, perform semantic analysis checks, expect no
     * semantic errors. Then translate into SEC machine code and run the code.
     * The value `expected` should be the output that we expect from this
     * run.
     */
    def execTest (str : String, expected : String) {
        val tree = parseProgram (str)
        /*
        val analysis = new SemanticAnalysis (new ExpTree (tree))
        import analysis._
        val messages = analysis.errors (tree)
        // println (messages)
        assert (messages.length === 0)
        */

        val instrs = Translator.translate (tree)
        // println (instrs)

        val emitter = new StringEmitter ()
        val machine = new SECMachine (emitter)

        machine.run (instrs) match {
            case _ : machine.State =>
                // Terminated correctly in some state
                assertResult (expected + "\n", "wrong execution output") (emitter.result ())
            case machine.FatalError (message) =>
                fail (message)
        }
    }

    // Translation tests that check the byte code that is produced.
    // Used to narrow down faults during marking...

    def translateTest (str: String, expected : Frame) {
        val tree = parseProgram(str)
        val instrs = Translator.translate(tree)

        assertResult (expected, "wrong translation output") (instrs)
    }

    test ("IF: a true less-than conditional expression evaluates to the correct result") {
        execTest ("""
            |if (1 < 2) 15 else 0
            """.stripMargin,
            "15")
    }

    test ("a false less-than conditional expression evaluates to the correct result") {
        execTest ("""
            |if (4 < 2) 15 else 0
            """.stripMargin,
            "0")
    }

    test ("translate if(true) 3 else 4")
    {
        translateTest("if(true) 3 else 4",
            List(IBool(true), IBranch(List(IInt(3)),List(IInt(4))), IPrint()))
    }

    test ("LIST: list()") {
        execTest ("""
            |List()
            """.stripMargin,
            "List()")
    }

    test ("list (4, 3, 7)") {
        execTest ("""
            |List(4, 3, 7)
            """.stripMargin,
            "List(4, 3, 7)")
    }

    test ("APP EXP: head(List(2, 1, 4))") {
        execTest ("""
            |head(List(2, 1, 4))
            """.stripMargin,
            "2")
    }

    test ("BLOCK ONE DEF: a single def evaluates to the correct result") {
        execTest ("""
            |{
            |   val x : Int = 1;
            |   x
            |}
            |""".stripMargin,
            "1")
    }

    test ("a block with a calculation evaluates to the correct result") {
        execTest ("""
            |{
            |   val x : Int = 5;
            |   x + 4
            |}
            |""".stripMargin,
            "9")
    }

    test ("translate { val x : Int = 3; x + 4 }")
    {
        translateTest("{ val x : Int = 3; x + 4 }",
            List(IClosure("x",List(IVar("x"), IInt(4), IAdd(), IPopEnv())),
                 IInt(3), ICall(), IPrint()))
    }

    test ("BLOCK ONE DEF FUN: a block with a single function definition evaluates to the correct result") {
        execTest ("""
            |{
            |  val inc : Int => Int = (a : Int) => a + 1;
            |  inc(1)
            |}
            """.stripMargin,
            "2")
    }

    test ("a single function block evaluates to the correct result") {
        execTest ("""
            |{
            |  val f : Int => Int = (x : Int) => x;
            |  f
            |}
            """.stripMargin,
            "function of x")
    }

    test ("translate { val f ... ; f(4) }")
    {
        translateTest("{ val f : Int => Int = (x : Int) => 2 * x; f(4) }",
            List(IClosure("f",List(IVar("f"), IInt(4), ICall(), IPopEnv())),
                 IClosure("x",List(IInt(2), IVar("x"), IMul(), IPopEnv())),
                 ICall(), IPrint()))
    }

    test ("BLOCK MULT DEF: a multiple def block evaluates to the correct result (use first def)") {
        execTest ("""
            |{
            |  val x : Int = 1;
            |  val y : Int = 2;
            |  x
            |}
            """.stripMargin,
            "1")
    }

    test ("a multiple def block evaluates to the correct result (use second def)") {
        execTest ("""
            |{
            |  val x : Int = 1;
            |  val y : Int = 2;
            |  y
            |}
            """.stripMargin,
            "2")
    }

    test ("BLOCK MULT DEF FUN: a multiple function block evaluates to the correct result (use first fun)") {
        execTest ("""
            |{
            |  val f : Int => Int = (x : Int) => x + 1;
            |  def g(y : Int) : Int = y * 2;
            |  f(4)
            |}
            """.stripMargin,
            "5")
    }

    test ("translate { val f ... ; def g ... ; (f 4) + (g 4) }")
    {
        translateTest("{ val f : Int => Int = (x : Int) => x+1; def g(y : Int) : Int = y*2; f(4) + g(4)}",
            List(IClosure("f",List(IClosure("g",List(IVar("f"), IInt(4),
                ICall(), IVar("g"), IInt(4), ICall(), IAdd(), IPopEnv())),
                IClosure("y",List(IVar("y"), IInt(2), IMul(), IPopEnv())),
                ICall(), IPopEnv())),
                IClosure("x",List(IVar("x"), IInt(1), IAdd(), IPopEnv())),
                ICall(), IPrint()))
    }

    test ("BLOCK NESTED ONE DEF: simple block in block") {
        execTest ("""
            |{
            |  val c : Int = 7;
            |  {
            |    val d : Int = 4;
            |    c + d
            |  }
            |}
            """.stripMargin,
            "11")
    }

    test ("BLOCK NESTED ONE DEF FUN: backward reference is evaluated correctly (same group)") {
        execTest ("""
            |{
            |  val g : Int => Int = (x : Int) => x * 2;
            |  { val h : Int => Int = (y : Int) => g(y);
            |    h(3) }
            |}
            """.stripMargin,
            "6")
    }

    test ("a function using a val is evaluated correctly (1)") {
        execTest ("""
            |{
            |  val x : Int = 1;
            |  { val f : Int => Int = (y : Int) => x;
            |    f(4) }
            |}
            """.stripMargin,
            "1")
    }

    test ("a function using a val is evaluated correctly (2)") {
        execTest ("""
            |{
            |  val x : Int = 7;
            |  { val f : Int => Int = (y : Int) => y + x;
            |    f(4) }
            |}
            """.stripMargin,
            "11")
    }

    test ("BLOCK COMPLEX: a multiple function block with vals before and after evaluates to the correct result (use both funs)") {
        execTest ("""
            |{
            |  val w : Int = 7;
            |  val f : Int => Int = (x : Int) => x + 1;
            |  val g : Int => Int = (y : Int) => y * 2;
            |  { val z : Int = f(w);
            |    f(z) + g(4) }
            |}
            """.stripMargin,
            "17")
    }

    test ("call with call argument is evaluated correctly") {
        execTest ("""
            |{
            |  val inc : Int => Int = (x : Int) => x + 1;
            |  val dec : Int => Int = (x : Int) => x - 1;
            |  inc(dec(4))
            |}
            """.stripMargin,
            "4")
    }

    test ("translate { val w = 7;  ... ; val z = f(w); f(z) + g(4) }")
    {
        translateTest("""
            |{
            |  val w : Int = 7;
            |  val f : Int => Int = (x : Int) => x + 1;
            |  val g : Int => Int = (y : Int) => y * 2;
            |  val z : Int = f(w);
            |  f(z) + g(4)
            |}
            """.stripMargin,
            List(IClosure("w",List(IClosure("f",List(IClosure("g",
                List(IClosure("z", List(IVar("f"), IVar("z"), ICall(),
                IVar("g"), IInt(4), ICall(), IAdd(), IPopEnv())), IVar("f"),
                IVar("w"), ICall(), ICall(), IPopEnv())),
                IClosure("y",List(IVar("y"), IInt(2), IMul(),
                IPopEnv())), ICall(), IPopEnv())), IClosure("x",List(IVar("x"),
                IInt(1), IAdd(), IPopEnv())), ICall(), IPopEnv())), IInt(7),
                ICall(), IPrint()))
    }

    test ("SIMPLE MATCHES: translate match case 3 => 2")
    {
        translateTest("""
                |3 match
                |{
                |case 3 => 2
                |}
                """.stripMargin,
            List(IClosure("x", List(IVar("x"), IInt(3), IEqual(),
                          IBranch(List(IInt(2)), List(IInt(999))), IPopEnv())),
                 IInt(3), ICall(), IPrint()))
    }

    test ("execute match case 3 => 2")
    {
        execTest("""
                |3 match
                |{
                |case 3 => 2
                |}
                """.stripMargin,
                "2")
    }

    test ("execute match case 3 => 2 with 4")
    {
        execTest("""
                |4 match
                |{
                |case 3 => 2
                |}
                """.stripMargin,
                "999")
    }

    test ("execute match case false = 6")
    {
        execTest("""
                |{
                |  def foo(a : Bool) : Int = a match
                |  {
                |  case false => 6
                |  };
                |  1000 * foo(false) + foo(true)
                |}
                """.stripMargin,
                "6999")
    }

    test ("translate match case n = 2 * n")
    {
        translateTest("""
                |3 match
                |{
                |case n => 2 * n
                |}
                """.stripMargin,
            List(IClosure("x", List(IClosure("n", List(IInt(2), IVar("n"),
                 IMul(), IPopEnv())), IVar("x"), ICall(), IPopEnv())), IInt(3),
                 ICall(), IPrint()))
    }

    test ("execute match case n => 2 * n with 3")
    {
        execTest("""
                |3 match
                |{
                |case n => 2 * n
                |}
                """.stripMargin,
                "6")
    }

    test ("translate match case _ => 7")
    {
        translateTest("""
                |3 match
                |{
                |case _ => 7
                |}
                """.stripMargin,
            List(IClosure("x", List(IInt(7), IPopEnv())), IInt(3), ICall(),
                 IPrint()))
    }

    test ("execute match case _ = 7 with 3")
    {
        execTest("""
                |3 match
                |{
                |case _ => 7
                |}
                """.stripMargin,
                "7")
    }

    test ("FACTORIAL: translate fac")
    {
        translateTest("""
                |{
                |  def fac(a : Int) : Int = a match
                |  {
                |  case 0 => 1
                |  case n => n * fac (n - 1)
                |  };
                |  fac(3)
                |}
                """.stripMargin,
            List(IClosure("fac", List(IVar("fac"), IInt(3), ICall(),
                 IPopEnv())), IClosure("a", List(IClosure("x", List(IVar("x"),
                 IInt(0), IEqual(), IBranch(List(IInt(1)), List(IClosure("n",
                 List(IVar("n"), IVar("fac"), IVar("n"), IInt(1), ISub(),
                 ICall(), IMul(), IPopEnv())), IVar("x"), ICall())),
                 IPopEnv())), IVar("a"), ICall(), IPopEnv())), ICall(),
                 IPrint()))
    }

    test ("execute fac with 3")
    {
        execTest("""
                |{
                |  def fac(a : Int) : Int = a match
                |  {
                |  case 0 => 1
                |  case n => n * fac (n - 1)
                |  };
                |  fac(3)
                |}
                """.stripMargin,
                "6")
    }

    test ("LIST PATTERNS: execute case List()")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case List() => 5
                |  };
                |  1000 * foo(List()) + foo(List(3))
                |}
                """.stripMargin,
                "5999")
    }

    test ("execute case List(8)")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case List(8) => 4
                |  };
                |  1000 * foo(List(8)) + foo(List(3))
                |}
                """.stripMargin,
                "4999")
    }

    test ("execute case List(k)")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case List(k) => 3 * k + 1
                |  };
                |  1000 * foo(List(2)) + foo(List(3, 4))
                |}
                """.stripMargin,
                "7999")
    }

    test ("execute case List(_, u)")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case List(_, u) => u + 2
                |  };
                |  1000 * foo(List(2, 4)) + foo(List(3, 4, 5))
                |}
                """.stripMargin,
                "6999")
    }

    test ("execute case List(r, 1, s)")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case List(r, 1, s) => 2 * r + s
                |  };
                |  1000 * foo(List(3, 1, 2)) + foo(List(3, 4, 5))
                |}
                """.stripMargin,
                "8999")
    }

    test ("CONS PATTERNS: execute case 3::_")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case 3::_ => 2
                |  };
                |  1000 * foo(List(3, 4)) + foo(List(5))
                |}
                """.stripMargin,
                "2999")
    }

    test ("execute case g::h")
    {
        execTest("""
                |{
                |  def foo(s : List[Int]) : Int = s match
                |  {
                |  case g::h => g :: 4 :: h
                |  };
                |  foo(List(3, 5, 6))
                |}
                """.stripMargin,
                "List(3, 4, 5, 6)")
    }

    test ("execute len(List(7, 4, 7))")
    {
        execTest("""
                |{
                |  def len(s : List[Int]) : Int = s match
                |  {
                |  case List() => 0
                |  case _::t => 1 + len(t)
                |  };
                |  len(List(7, 4, 7))
                |}
                """.stripMargin,
                "3")
    }

    // ================================================================
    //
    // FIXME: more tests here...

    test("START OF ADDITIONAL TESTS: Pre-defined list operation and user-defined list operation - Tail") {
        execTest("""
        {
            val arr: List[Int] = List(1, 2, 3, 4);
            def listTail(list:List[Int]):List[Int] = list match {
                case h :: t => t
                case _ => List(0)
            };
            tail(arr) == listTail(arr)
        }
        """.stripMargin,
        "true")
    }

    test("Pre-defined list operation and user-defined list operation - Head") {
        execTest("""
        {
            val arr: List[Int] = List(1, 2, 3, 4);
            def listHead(list:List[Int]):Int = list match {
                case h :: t => h
                case _ => 0
            };
            head(arr) == listHead(arr)
        }
        """.stripMargin,
        "true")
    } 

    test("Pre-defined list operation and user-defined list operation - Length") {
        execTest("""
        {
            val arr: List[Int] = List(1, 2, 3, 4);
            def listLength(list:List[Int]):Int = list match {
                case h :: t => 1 + listLength(t)
                case _ => 0
            };
            length(arr) == listLength(arr)
        }
        """.stripMargin,
        "true")
    }

    test("Get list head then cons to existing list") {
        execTest("""
        {
            val arr : List[Int] = List(7, 8, 9);
            def getHead(l:List[Int]):List[Int] = l match {
                case h :: t => h
            };
            def pushOne(v:List[Int]):List[Int] = 1 :: v;
            getHead((2::(1 :: arr))) :: pushOne(arr)
        }
        """.stripMargin,
        "List(2, 1, 7, 8, 9)")
    }      

    test("Fibonnaci function") {
        execTest("""
            {
                val x : Int = 9;
                def fibonnaci(n:Int):Int = 
                    n match {
                        case 0 => 0
                        case 1 => 1
                        case _ => fibonnaci(n - 1) + fibonnaci(n - 2)
                    };
                fibonnaci(x)
            } 
        """.stripMargin,
        "34")
    }   

    test ("Perform operation on variable with block statement as value") {
        execTest ("""
            {
               val num : Int = 90;
               val x: Int = {
                   val y : Int = 23;
                   def triple(x:Int):Int = x * 3;
                   if (triple(y) * triple(y) < triple(triple(y)))
                       y
                   else
                       triple(y)
               };
               def sum(i:Int):Int = i match {
                   case 300 => i - num
                   case _ => i + num
               };
               sum(x)
            }
            """.stripMargin,
            "159")
    }

    test ("Operate on multiple and bracketed block statements") {
        execTest ("""
            {
                val a : Int = 5;
                def fac(x:Int):Int = x match {
                    case 0 => 1
                    case a => a * fac(a - 1)
                    case _ => 1
                };
                fac(a) * 2
            } 
            /
            (
                {
                    def square(x:Int):Int = x * x;
                    square(5)
                }
                +
                {
                    val a : Int = 2;
                    val b : Int = 5;
                    val c : Int = 10;
                    ((x:Int) => 1 + ((y:Int) => y * 2)(x)) (a) * b + c
                }
            )
            """.stripMargin,
            "4")
    }

    test ("Translate def function to val function and operate with it") {
        execTest ("""
            {
               val a : Int = 100;
               val multiplyTen : Int = (num:Int) => num * 10;
               def sum(i:Int):Int = i + 50;
               multiplyTen(sum(a))
            }
            """.stripMargin,
            "1500")
    }

    test ("Translate bits into an integer") {
        execTest ("""
            {
                val bits : List[Int] = List(1, 1, 1, 0, 0, 1, 0, 1);
                def powerOfTwo(n:Int):Int = n match {
                    case 0 => 1
                    case _ => 2 * powerOfTwo(n - 1)
                };
                def getLength(l:List[Int]):Int = l match {
                    case h :: t => 1 + getLength(t)
                    case _ => 0
                };
                def translateBits(l:List[Int]):Int = l match {
                        case 1::t => powerOfTwo(getLength(l) - 1) + translateBits(t)
                        case 0::t => translateBits(t)
                        case _ => 0
                    };
                translateBits(bits)
            }
            """.stripMargin,
            "229")
    }
}

