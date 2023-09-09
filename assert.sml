(* This is a unit test framework in SML
 * !!! <- implies the function needs to be changed later *)

signature assert =
sig
  type assertType
  val isTrue : bool -> unit
  val isFalse : bool -> unit

  val equalInt : int -> int -> unit
  val equalChar : char -> char -> unit
  val equalString : string -> string -> unit
  val equalReal : real -> real -> unit
  val equalRealEps : real -> real -> real -> unit

  val equalOptInt : int option -> int option -> unit
  val equalOptChar : char option -> char option -> unit
  val equalOptString : string option -> string option -> unit
  val equalOptReal : real option -> real option -> unit
  val equalOptRealEps : real option -> real option -> real -> unit

  val trueTuple : ''a -> ''a -> unit
  val equalTuple : ''a -> ''a -> (''a -> string) -> unit
  val trueTupleDT : 'a -> 'b -> ('a * 'b -> bool) -> unit
  val equalTupleDT : 'a -> 'a -> ('a * 'a -> bool) -> ('a -> string) -> unit

  val trueDT : 'a -> 'b -> ('a * 'b -> bool) -> unit
  val equalDT : 'a -> 'a -> ('a * 'a -> bool) -> ('a -> string) -> unit

  val trueList : ''a -> ''a -> unit
  val trueListDT : 'a  -> 'b -> ('a * 'b -> bool) -> unit
  val equalListInt : int list -> int list -> unit
  val equalListReal : real list -> real list -> unit
  val equalListRealEps : real list -> real list -> real -> unit
  val equalListChar : char list -> char list -> unit
  val equalListString : string list -> string list -> unit
  val equalListDT : 'a -> 'a  -> ('a * 'a -> bool) -> ('a -> string) -> unit
end;

structure Assert :> assert =
struct

datatype assertType = Passed of string
                    | NotEqual of string * string
                    | GeneralFailure of string

(* ('a * 'a -> bool) 'a 'a ('a -> string) -> assertType
 * Checks if two values are equal to each other
 * it also takes a function that can compare both values
 * and a function to convert the value to a string *)
fun equal compareFun actVal expVal valToStr =
    if compareFun (actVal, expVal)
    then Passed("Passed test!\n")
    else
      let val actSt = valToStr actVal
          val expSt = valToStr expVal
      in
        NotEqual(actSt, expSt)
      end


(* ('a option * 'a option -> bool) 'a option 'a option ('a -> string)
   -> assertType
 * Checks if two Option values are equal to each other
 * it also takes a function that can compare both values
 * and a function to convert the value to a string *)
fun equalOption compareFun actVal expVal valToStr =
    case (actVal, expVal) of
        (NONE, _) => GeneralFailure("Failed test.\nOne option is NONE.\n")
      | (_ ,NONE) => GeneralFailure("Failed test.\nOne option is NONE.\n")
      | (SOME x, SOME y) =>
        equal compareFun (valOf actVal) (valOf expVal) valToStr

(* asserttype -> unit 
 * Helper function to print isTrue/isFalse functions *)
fun boolPrint (Passed(x)) = print x
  | boolPrint (GeneralFailure(x)) = print x;

(* bool -> unit
 * Checks if it's true *)
fun isTrue boolean =
    if boolean then boolPrint (Passed("Passed test!\n"))
    else boolPrint (GeneralFailure("Failed test.\nExpected <true> value.\n"))

(* bool -> unit
 * Checks if it's false *)
fun isFalse boolean =
    if not boolean then boolPrint (Passed("Passed test!\n"))
    else boolPrint (GeneralFailure("Failed test.\nExpected <false> value.\n"))

(* assertType -> unit
 * Prints passed or not passed
 * For not passed, it can either just print not passed or
 * also print the expected and actual values too
 * !!! *)
fun equalPrint (Passed(x)) = print x
  | equalPrint (GeneralFailure(x)) = print x
  | equalPrint (NotEqual(x,y)) =
    print ("Not equal!\n" ^
           "Actual value is <" ^ x ^ ">\nExpected value is <" ^ y ^ ">\n")

(* int int -> unit
 * Checks if two ints are equal *)
fun equalInt act exp =
    equalPrint (equal (op=) act exp Int.toString)

(* (int option) (int option) -> unit
 * Checks if two int options are equal *)
fun equalOptInt act exp =
    equalPrint (equalOption (op=) act exp Int.toString)

(* char char -> unit
 * Checks if two chars are equal *)
fun equalChar act exp =
    equalPrint (equal (op=) act exp Char.toString)

(* (char option) (char option) -> unit
 * Checks if two char options are equal *)
fun equalOptChar act exp =
    equalPrint (equalOption (op=) act exp Char.toString)

(* string string -> unit
 * checks if two strings are equal *)
fun equalString act exp =
    equalPrint (equal (op=) act exp String.toString)

(* (string option) (string option) -> unit
 * checks if two string options are equal *)
fun equalOptString act exp =
    equalPrint (equalOption (op=) act exp String.toString)

(* real real -> unit
 * checks if two reals are equal *)
fun equalReal act exp =
    equalPrint (equal Real.== act exp Real.toString)

(* (real option) (real option) -> unit
 * checks if two real options are equal *)
fun equalOptReal act exp =
    equalPrint (equalOption Real.== act exp Real.toString)

(* real real real -> unit
 * checks if two reals are epsilon-close *)
fun equalRealEps act exp eps =
    equalPrint (equal
                    (fn (x,y) => Real.<=(y-eps,x)
                                 andalso Real.<=(x, y+eps))
                    act exp Real.toString)


(* (real option) (real option) real -> unit
 * checks if two real options are epsilon-close *)
fun equalOptRealEps act exp eps =
    equalPrint (equalOption
                    (fn (x,y) => Real.<=(y-eps,x)
                                 andalso Real.<=(x, y+eps))
                    act exp Real.toString)

(* Tuples have a problem that you can't access any elements of it if
 * we don't use matching pattern for it(fn (a,b,c) instead of
 * fn v for a triple) which means that we can't just create a
 * pattern for every n-tuple.
 * Also, we have two cases:
 * a) it's a tuple of basic data type
 * b) it's a tuple of user-defined data types:
 * For each case, we have two options:
 * 1) Just check if they are equal, thus assertTrue is enough
 * 2) Check if they are equal and print expected and actual value if false
 * For the second option, we need to ask the user to include a function to
 * print values since it depends heavily on the number of elements in a tuple
 * for case b), we also need the user to include a compare function for its
 * user-defined datatype.
 * For both cases, the compare function shoudl take into account
 * the number of tuple elements *)

(* tuple tuple -> unit
 * checks if the two basic data types tuples are equal *)
fun trueTuple act exp =                                   (* a-1 *)
    isTrue (act = exp)

(* tuple tuple (tuple -> string) -> unit
 * checks if two basic data types tuples are equal
 * and is able to print values if they are not *)
fun equalTuple act exp valToStr =                     (* a-2 *)
    equalPrint (equal (op=) act exp valToStr)


(* tuple tuple (tuple * tuple -> bool) -> unit
 * checks if the two user-defined data types tuples are equal *)
fun trueTupleDT act exp compareFun =                     (* b-1 *)
    (isTrue o compareFun) (act,exp)

(* tuple tuple (tuple * tuple -> bool) (tuple -> string) -> unit
 * checks if two user-defined data types tuples are equal
 * and is able to print values if they are not *)
fun equalTupleDT act exp compareFun valToStr =      (* b-2 *)
    equalPrint (equal compareFun act exp valToStr)

(* For user-defined datatypes, we follow the same idea for the tuple DT cases *)

(* 'a datatype 'a datatype ('a datatype * 'a datatype -> bool) -> unit
 * checks if two value of 'a datatype are equal *)
fun trueDT act exp compareFun =
    (isTrue o compareFun) (act,exp)

(* 'a datatype 'a datatype ('a datatype * 'a datatype -> bool) ('a datatype > string)
   -> unit
 * checks if two value of 'a datatype are equal and print values if they are not *)
fun equalDT act exp compareFun valToStr =
    equalPrint (equal compareFun act exp valToStr)

(* Lists follow the same idea of tuples, equality of basic datatypes does not require
 * the user to define a new compare function. However, printing lists values is
 * not defined by the Basis Library, so the user would have to define one for each
 * basic datatype. Unlike tuples, we can access every value of the list using
 * matching pattern and so don't need to create a pattern for every n value of the list.
 * Thus, we are going to follow something similar to tuples.
 * For user-defined datatypes, the user must input a compare function and, in the case
 * of wanting to print expected and actual values, a print function. *)

(* 'a list 'a list ('a * 'a -> bool) -> unit
 * checks if two lists of datatypes are equal *)
fun trueListDT act exp compareFun =
    (isTrue o compareFun) (act,exp)

(* 'a list 'a list -> unit
 * check if two lists of basic datatypes are equal *)
fun trueList act exp =
    isTrue (exp=act)

(* 'a list 'a list ('a * 'a -> bool) (a' list -> string) -> unit
 * checks if two lists of basic datatypes are equal
 * and prints their value if not *)
fun equalList act exp compareFun valToStr =
    equalPrint (equal compareFun act exp valToStr)

(* int list -> string
 * returns a readable form of a int list *)
fun intlistToStr xs =
    let
      fun intlistToStr' [] = "]"
        | intlistToStr' [x] = Int.toString x ^ "]"
        | intlistToStr' (x::xs) = Int.toString x ^ "," ^ intlistToStr' xs
    in
      "[" ^ intlistToStr' xs
    end

(* int list int list  -> unit
 * checks if two int lists are equal and prints their value if not *)
fun equalListInt act exp =
    equalList act exp (op=) intlistToStr

(* real list -> string
 * returns a readable form of a real list *)
fun reallistToStr xs =
    let
      fun reallistToStr' [] = "]"
        | reallistToStr' [x] = Real.toString x ^ "]"
        | reallistToStr' (x::xs) = Real.toString x ^ "," ^ reallistToStr' xs
    in
      "[" ^ reallistToStr' xs
    end

(* real list * real list -> bool
 * compare values of two real lists *)
fun realEquality ([],[])        = true
  | realEquality ([], _)        = false
  | realEquality (_, [])        = false
  | realEquality (x::xs, y::ys) =
    Real.==(x,y) andalso realEquality (xs,ys)

(* real list real list -> unit
 * checks if two real lists are equal and prints their value if not *)
fun equalListReal act exp =
    equalList act exp realEquality reallistToStr


(* real list * real list * real -> bool
 * compare epsilon-closeness of two real lists *)
fun realCloseEps e ([],[])        = true
  | realCloseEps e ([], _)        = false
  | realCloseEps e (_, [])        = false
  | realCloseEps e (x::xs, y::ys) =
    Real.<=(y-e,x) andalso Real.<=(x, y+e)
    andalso realCloseEps e (xs,ys)

(* real list real list real -> unit
 * checks if two real lists are epsilon-close
 * and prints their value if not *)
fun equalListRealEps act exp eps =
    equalList act exp  (realCloseEps eps) reallistToStr


(* char list -> string
 * returns a readable form of a char list *)
fun charlistToStr xs =
    let
      fun charlistToStr' [] = "]"
        | charlistToStr' [x] = Char.toString x ^ "]"
        | charlistToStr' (x::xs) = Char.toString x ^ "," ^ charlistToStr' xs
    in
      "[" ^ charlistToStr' xs
    end

(* char list char list -> unit
 * checks if two int lists are equal and prints their value if not *)
fun equalListChar act exp =
    equalList act exp (op=) charlistToStr

(* string list -> string
 * returns a readable form of a string list *)
fun stringlistToStr xs =
    let
      fun stringlistToStr' [] = "]"
        | stringlistToStr' [x] = x ^ "]"
        | stringlistToStr' (x::xs) = x ^ "," ^ stringlistToStr' xs
    in
      "[" ^ stringlistToStr' xs
    end

(* string list string list -> unit
 * checks if two string lists are equal and prints their value if not *)
fun equalListString act exp =
    equalList act exp (op=) stringlistToStr


(* 'a datatype list  'a datatype list  ('a datatype list * 'a datatype list
 -> bool ) ('a datatype -> string) -> unit
 * checks if two datatype lists are equal and prints their value
 * if not.
 * The user must define both the compare function and print function *)
fun equalListDT act exp compareFun dtlistToStr =
    equalList act exp compareFun dtlistToStr
end
