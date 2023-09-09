signature word16 =
sig
  (* our word16 is just word but restricting to 16 bits *)
  type word16 = Word.word

  val wordSize  : int
  val maxWord16 : int

  val fromInt   : int -> word16
  val toInt     : word16 -> int
  val fromWord  : Word.word -> word16
  val toWord    : word16 -> Word.word

  val orb       : word16 * word16 -> word16
  val xorb      : word16 * word16 -> word16
  val andb      : word16 * word16 -> word16
  val notb      : word16  -> word16

  val shiftl    : word16 * word16 -> word16
  val shiftr    : word16 * word16 -> word16

  val add       : word16 * word16 -> word16
  val sub       : word16 * word16 -> word16
  val modw      : word16 * word16 -> word16
  val divw      : word16 * word16 -> word16

end;

structure Word16 :> word16 =
struct
type word16 = Word.word
val wordSize = 16
val maxWord16 = 65535
(* internal variable for masking *)
val maxWord = Word.fromInt 65535

fun fromInt n = Word.andb(Word.fromInt n, maxWord)
fun toInt   a = Word.toInt a;

fun fromWord w = fromInt (Word.toInt w);
fun toWord   a = Word.fromInt (toInt a);

(* We just reuse the functions from Word,
 * since OR, XOR and AND are closed *)
fun orb  (a,b) = Word.orb(a,b)
fun xorb (a,b) = Word.xorb(a,b)
fun andb (a,b) = Word.andb(a,b)

(* For not, we have to use XOR with the 0xFFFF
 * so we can 0 any bits bigger than it *)
fun notb a = Word.xorb(maxWord, a)

(* we need to mask a + b and a - b since
 * it can result in a number bigger than 0xFFFF *)
fun add (a,b) = Word.andb(Word.+(a,b), maxWord)
fun sub (a,b) = Word.andb(Word.-(a,b), maxWord)
fun modw (a,b) = Word.mod(a,b)
fun divw (a,b) = Word.div(a,b)

fun shiftl (a,b) = andb(Word.<<(a,b), maxWord)
fun shiftr (a,b) = Word.>>(a,b)
end;
