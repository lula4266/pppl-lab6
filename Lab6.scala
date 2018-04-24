package jsy.student

import jsy.lab6.Lab6Like
import jsy.lab6.ast._
import jsy.student.Lab6.test
import jsy.util.DoWith

object Lab6 extends jsy.util.JsyApplication with Lab6Like {

  /*
   * CSCI 3155: Lab 6
   * <Xi Gao>
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*** Exercises with Continuations ***/

  def foldLeftAndThen[A,B](t: Tree)(z: A)(f: (A,Int) => A)(sc: A => B): B = {
    def loop(acc: A, t: Tree)(sc: A => B): B = t match {
      case Empty => sc(acc)
      case Node(l, d, r) => loop(acc, l) { lacc => loop(f(lacc, d), r)(sc) }
    }
    loop(z, t)(sc)
  }

  def dfs[A](t: Tree)(f: Int => Boolean)(sc: List[Int] => A)(fc: () => A): A = {
    def loop(path: List[Int], t: Tree)(fc: () => A): A = {
      t match {
        case Empty => fc()
        case Node(l, d, r) => {
          loop(d :: path, l) { () => if (f(d)) sc(d :: path) else loop(d :: path, r)(fc) }
        }
      }
    }
    loop(Nil, t)(fc)
  }

  /*** Regular Expression Parsing ***/

  /* We define a recursive decent parser for regular expressions in
   * REParser.
   * 
   * The REParserLike trait derives from Parsers in the Scala library to make
   * use of it's handing of input (Input) and parsing results (ParseResult).
   * 
   * The Parsers trait is actually a general purpose combinator parser library,
   * which we won't use directly.
   *
   * Grammar. You will want to write a BNF grammar here from your write-up
   * as the basis for your implementation.
   *
   *   re ::= union
   *
   *   union ::= intersect unions
   *   unions ::= epsilon | '|' intersect unions
   *
   *   intersect ::= ???
   *   concat ::= ???
   *   not ::= ???
   *   star ::= ???
   *   atom ::= ???
   * 
   */
  object REParser extends REParserLike {
    /* The following items are the relevant pieces inherited from Parsers
     * 
     * type Input = Reader[Char]
     * sealed abstract class ParseResult[T] {
     *   val next: Input
     *   def map[U](f: T => U): ParseResult[U]
     * }
     * case class Success[T](result: T, next: Input) extends ParseResult[T]
     * case class Failure(next: Input) extends ParseResult[Nothing]
     */

    def re(next: Input): ParseResult[RegExpr] = union(next) // calls union with next

    def union(next: Input): ParseResult[RegExpr] = intersect(next) match {
      case Success(r, next) => { // if intersect returns success
        def unions(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next) // if at end of input, return success
          else (next.first, next.rest) match { // if not at end, match next char
            case ('|', next) => intersect(next) match { // matches union
              case Success(r, next) => unions(RUnion(acc, r), next) // if intersect returns success, do union on acc and r
              case _ => Failure("expected intersect", next) // if intersect returns failure, return fail error
            }
            case _ => Success(acc, next) // if not union, return success with acc and next
          }
        unions(r, next) // calls unions on r and next
      }
      case _ => Failure("expected intersect", next) // if intersect doesn't return success, returns fail error
    }

    def intersect(next: Input): ParseResult[RegExpr] = concat(next) match {
      case Success(r, next) => { // if concat returns success
        def intersects(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next) // if at end, returns success with acc and next
          else (next.first, next.rest) match { // if not at end, match next char
            case ('&', next) => concat(next) match { // matches intersection
              case Success(r, next) => intersects(RIntersect(acc, r), next) // if concat returns success do intersect on it
              case _ => Failure("expected concat", next) // if concat returns failure, returns fail error
            }
            case _ => Success(acc, next) // if not intersection, return success with acc and next
          }
        intersects(r, next) // calls intersects with r and next
      }
      case _ => Failure("expected concat", next) // if concat doesn't return success, return fail error
    }

    def concat(next: Input): ParseResult[RegExpr] = not(next) match {
      case Success(r, next) => { // if not return a success
        def concats(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next) // if at end of input, return success
          else not(next) match { // if not at end call next again
            case Success(r, next) => concats(RConcat(acc, r), next) // if success, do concats
            case _ => Success(acc, next) // just return the acc and next
          }
        concats(r, next) // calls concat on r and next
      }
      case _ => Failure("expected not", next) // if not returns failure
    }

    def not(next: Input): ParseResult[RegExpr] = (next.first, next.rest) match {
      case ('~', next) => not(next) match { // matches not
        case Success(r, next) => Success(RNeg(r), next) // matches if success return
        case fail => fail // returns fail error
      }
      case _ => star(next) match { // matches if not not
        case Success(r, next) => Success(r, next) // matches if star returns a success
        case fail => fail // returns fail error
      }
    }

    def star(next: Input): ParseResult[RegExpr] = atom(next) match { // matches return of atom
      case Success(r, next) => { // if atom returns a success
        def stars(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next) // if at end of next, return success
          else (next.first, next.rest) match { // if not at end, match first char
            case ('*', next) => stars(RStar(acc),next) // matches kleene star
            case ('+', next) => stars(RPlus(acc), next) // matches 1 or more
            case ('?', next) => stars(ROption(acc), next) // matches 0 or more
            case _ => Success(acc, next) // return success for anything else
          }
        stars(r, next) // calls stars with r and next
      }
      case _ => Failure("expected atom", next) // if atom doesn't return success
    }

    /* This set is useful to check if a Char is/is not a regular expression
       meta-language character.  Use delimiters.contains(c) for a Char c. */
    val delimiters = Set('|', '&', '~', '*', '+', '?', '!', '#', '.', '(', ')')

    def atom(next: Input): ParseResult[RegExpr] = {
      if (next.atEnd) Failure("empty or unable to match", next) // if end of input, return failure due to no match or empty input
      else (next.first, next.rest) match { // splits first char and rest of input
        case ('!', next) => Success(RNoString, next) // matches no string
        case ('#', next) => Success(REmptyString, next) // matches empty string
        case ('.', next) => Success(RAnyChar, next) // matches any character
        case ('(', next) => re(next) match { // calls re on next character in input
          case Success(reast, next) => (next.first, next.rest) match { // matches a successful return
            case (')', next) => Success(reast, next) // // matches successful closing of parenthesis
            case _ => Failure("expected )", next) // matches when grouping not closed
          }
          case fail => fail // returns fail error
        }
        case (c, next) if !delimiters.contains(c) => Success(RSingle(c), next) // matches if c is not a delimiter
        case _ => Failure("expected atom", next) // matches if not an atom
      }
    }

  }


  /***  Regular Expression Matching ***/

  /** Tests whether a prefix of chars matches the regular expression re with a continuation for the suffix.
    *
    * @param re a regular expression
    * @param chars a sequence of characters
    * @param sc the success continuation
    * @return if there is a prefix match, then sc is called with the remainder of chars that has yet to be matched. That is, the success continuation sc captures “what to do next if a prefix of chars successfully matches re; if a failure to match is discovered, then false is returned directly.
    */
  def test(re: RegExpr, chars: List[Char])(sc: List[Char] => Boolean): Boolean = (re, chars) match {
    /* Basic Operators */
    case (RNoString, _) => false // returns false if matched with anything
    case (REmptyString, _) => sc(chars) // checks to see if empty string
    case (RSingle(_), Nil) => false // returns false if empty string
    case (RSingle(c1), c2 :: t) => c1 == c2 && sc(t) // checks if character matches and if it is a single character
    case (RConcat(re1, re2), _) => test(re1, chars) { sfx => test(re2, sfx)(sc) } // tests if re2 is true; then checks if re1 is true
    case (RUnion(re1, re2), _) => test(re1, chars)(sc) || test(re2, chars)(sc)  // tests if re1 OR re2 is true
    case (RStar(re1), _) => sc(chars) || test(re1, chars) { sfx => sfx != chars && test(RStar(re1), sfx)(sc) } // checks if in 0 or more concats

    /* Extended Operators */
    case (RAnyChar, Nil) => false // returns false if empty string
    case (RAnyChar, _ :: t) => sc(t) // checks if it is a single character
    case (RPlus(re1), _) => test(RConcat(re1, RStar(re1)), chars)(sc) // checks if in 1 or more concats
    case (ROption(re1), _) => sc(chars) || test(re1, chars)(sc) // checks if matches with 0 or more re

    /***** Extra Credit Cases *****/
    case (RIntersect(re1, re2), _) => ???
    case (RNeg(re1), _) => ???
  }

  def retest(re: RegExpr, s: String): Boolean = test(re, s.toList) { chars => chars.isEmpty }


  /*******************************/
  /*** JavaScripty Interpreter ***/
  /*******************************/

  /* This part is optional for fun and extra credit.
   *
   * If you want your own complete JavaScripty interpreter, you can copy your
   * Lab 5 interpreter here and extend it for the Lab 6 constructs.
   */

  /*** Type Inference ***/

  def typeof(env: TEnv, e: Expr): Typ = ???

  /*** Step ***/

  def substitute(e: Expr, v: Expr, x: String): Expr = ???
  def step(e: Expr): DoWith[Mem,Expr] = ???

  /*** Lower ***/

  def lower(e: Expr): Expr = e

}