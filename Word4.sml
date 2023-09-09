signature word4 =
sig
  (* our word4 is just word8 but restricting to 4 bits *)
  type word4 = Word8.word

  val wordSize  : int
  val maxWord4  : int

  val fromInt   : int -> word4
  val toInt     : word4 -> int
  val toWord    : word4 -> word
  val fromWord  : word -> word4

  val orb       : word4 * word4 -> word4
  val xorb      : word4 * word4 -> word4
  val andb      : word4 * word4 -> word4
  val notb      : word4  -> word4

  val shiftl    : word4 * word4 -> word4
  val shiftr    : word4 * word4 -> word4

  val add       : word4 * word4 -> word4
  val sub       : word4 * word4 -> word4
  val modw      : word4 * word4 -> word4
  val divw      : word4 * word4 -> word4

end;

structure Word4 :> word4 =
struct
type word4 = Word8.word
val wordSize = 4
val maxWord4 = 15
(* internal variable for masking *)
val maxWord = Word8.fromInt 15

fun fromInt n = Word8.andb(Word8.fromInt n, maxWord)
fun toInt   a = Word8.toInt a;

fun fromWord w = fromInt (Word.toInt w);
fun toWord   a = Word.fromInt (toInt a);

(* We just reuse the functions from Word,
 * since OR, XOR and AND are closed *)
fun orb  (a,b) = Word8.orb(a,b)
fun xorb (a,b) = Word8.xorb(a,b)
fun andb (a,b) = Word8.andb(a,b)

(* For not, we have to use XOR with the 0xFFFF
 * so we can 0 any bits bigger than it *)
fun notb a = Word8.xorb(maxWord, a)

(* we need to mask a + b and a - b since
 * it can result in a number bigger than 0xFFFF *)
fun add (a,b)  = Word8.andb(Word8.+(a,b), maxWord)
fun sub (a,b)  = Word8.andb(Word8.-(a,b), maxWord)
fun modw (a,b) = Word8.mod(a,b)
fun divw (a,b) = Word8.div(a,b)

(* Word8 >> and << takes a Word31 variable as its second input
 * but we can't convert from Word8 to Word31 directly,
 * we first need to convert to Word32 and then back to Word31 *)
val convertWord = (Word31.fromLargeWord o Word8.toLarge)

fun shiftl (a,b) = andb(Word8.<<(a, convertWord b), maxWord)
fun shiftr (a,b) = Word8.>>(a, convertWord b)
end;
