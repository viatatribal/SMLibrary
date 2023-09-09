(* Implementation of an MD5-compatible hash function.
   From https://www.ietf.org/rfc/rfc1321.txt *)

signature MD5 =
sig

  (* Perform the MD5 hash function on a message.
     Returns the 128 bit (16 byte) hash. *)
  val md5hash : string -> string

  (* Returns the hex version of a MD5 hash *)
  val md5 : string -> string
end

structure MD5 :> MD5 =
struct

structure W32 = Word32
structure W8 = Word8
val orb  = W32.orb
val xorb = W32.xorb
val andb = W32.andb
val notb = W32.notb
val <<   = W32.<<
val >>   = W32.>>
infix xorb andb orb << >>

(* Convert from word to bit *)
fun wToBit w =
    map
       chr
    [W8.toInt (W8.fromLarge w), W8.toInt (W8.fromLarge (w >> 0w8)),
     W8.toInt (W8.fromLarge (w >> 0w16)), W8.toInt (W8.fromLarge (w >> 0w24))]

(* Convert from bit to word *)
fun bToWord (a, b, c, d) =
    (W32.fromInt (ord a)) +
    (W32.fromInt (ord b) << 0w8)  +
    (W32.fromInt (ord c) << 0w16) +
    (W32.fromInt (ord d) << 0w24)

(* Does Step 1 of the algorithm: Append padding bits
 * to the message so it's congruent to 56 bytes mod 64 *)
fun appendPad msg size =
    let
      val len = size mod 64
      val pad = if len < 56 then 56 - len else 120 - len
    in
      msg ^ (str (chr 0x80)) ^
      implode (List.tabulate (pad - 1, fn _ => chr 0))
    end

(* Does Step 2 of the algorithm: Append the length of
 * of the message in a 64-bit representation to the message*)
fun appendLen msg size =
    msg
    ^ implode (wToBit (W32.fromInt (size * 8)))
    ^ implode (List.tabulate (4, fn _ => chr 0))

(* Convert string to Word32 *)
val stow = (Option.valOf o W32.fromString
           )
(* Our initial values for Step 3 *)
val A = stow "0x67452301"
val B = stow "0xefcdab89"
val C = stow "0x98badcfe"
val D = stow "0x10325476"

(* Auxiliar functions for Step 4 *)
fun F (x,y,z) = (x andb y) orb (notb x andb z)
fun G (x,y,z) = (x andb z) orb (y andb notb z)
fun H (x,y,z) = x xorb y xorb z
fun I (x,y,z) = y xorb (x orb notb z)
(* Does circular left rotation *)
fun LR(x,n) = (x << n) orb ( x >> (0w32 - n))

fun FF (a, b, c, d, x, s, ac) =
    LR (a + F(b,c,d) + x + ac, s) + b
fun GG (a, b, c, d, x, s, ac) =
    LR (a + G(b,c,d) + x + ac, s) + b
fun HH (a, b, c, d, x, s, ac) =
    LR (a + H(b,c,d) + x + ac, s) + b
fun II (a, b, c, d, x, s, ac) =
    LR (a + I(b,c,d) + x + ac, s) + b

(* Apply the auxiliar functions to our initial values and
 * message *)
fun transformations (aa, bb, cc, dd) xj =
    let
      val a = aa
      val b = bb
      val c = cc
      val d = dd

      (* Round 1 *)
      val a = FF (a, b, c, d, xj  0, 0w7,  stow "0xd76aa478")
      val d = FF (d, a, b, c, xj  1, 0w12, stow "0xe8c7b756")
      val c = FF (c, d, a, b, xj  2, 0w17, stow "0x242070db")
      val b = FF (b, c, d, a, xj  3, 0w22, stow "0xc1bdceee")
      val a = FF (a, b, c, d, xj  4, 0w7,  stow "0xf57c0faf")
      val d = FF (d, a, b, c, xj  5, 0w12, stow "0x4787c62a")
      val c = FF (c, d, a, b, xj  6, 0w17, stow "0xa8304613")
      val b = FF (b, c, d, a, xj  7, 0w22, stow "0xfd469501")
      val a = FF (a, b, c, d, xj  8, 0w7,  stow "0x698098d8")
      val d = FF (d, a, b, c, xj  9, 0w12, stow "0x8b44f7af")
      val c = FF (c, d, a, b, xj 10, 0w17, stow "0xffff5bb1")
      val b = FF (b, c, d, a, xj 11, 0w22, stow "0x895cd7be")
      val a = FF (a, b, c, d, xj 12, 0w7,  stow "0x6b901122")
      val d = FF (d, a, b, c, xj 13, 0w12, stow "0xfd987193")
      val c = FF (c, d, a, b, xj 14, 0w17, stow "0xa679438e")
      val b = FF (b, c, d, a, xj 15, 0w22, stow "0x49b40821")

      (* Round 2*)
      val a = GG (a, b, c, d, xj  1, 0w5,  stow "0xf61e2562")
      val d = GG (d, a, b, c, xj  6, 0w9,  stow "0xc040b340")
      val c = GG (c, d, a, b, xj 11, 0w14, stow "0x265e5a51")
      val b = GG (b, c, d, a, xj  0, 0w20, stow "0xe9b6c7aa")
      val a = GG (a, b, c, d, xj  5, 0w5,  stow "0xd62f105d")
      val d = GG (d, a, b, c, xj 10, 0w9,  stow "0x02441453")
      val c = GG (c, d, a, b, xj 15, 0w14, stow "0xd8a1e681")
      val b = GG (b, c, d, a, xj  4, 0w20, stow "0xe7d3fbc8")
      val a = GG (a, b, c, d, xj  9, 0w5,  stow "0x21e1cde6")
      val d = GG (d, a, b, c, xj 14, 0w9,  stow "0xc33707d6")
      val c = GG (c, d, a, b, xj  3, 0w14, stow "0xf4d50d87")
      val b = GG (b, c, d, a, xj  8, 0w20, stow "0x455a14ed")
      val a = GG (a, b, c, d, xj 13, 0w5,  stow "0xa9e3e905")
      val d = GG (d, a, b, c, xj  2, 0w9,  stow "0xfcefa3f8")
      val c = GG (c, d, a, b, xj  7, 0w14, stow "0x676f02d9")
      val b = GG (b, c, d, a, xj 12, 0w20, stow "0x8d2a4c8a")

      (* Round 3*)
      val a = HH (a, b, c, d, xj  5, 0w4,  stow "0xfffa3942")
      val d = HH (d, a, b, c, xj  8, 0w11, stow "0x8771f681")
      val c = HH (c, d, a, b, xj 11, 0w16, stow "0x6d9d6122")
      val b = HH (b, c, d, a, xj 14, 0w23, stow "0xfde5380c")
      val a = HH (a, b, c, d, xj  1, 0w4,  stow "0xa4beea44")
      val d = HH (d, a, b, c, xj  4, 0w11, stow "0x4bdecfa9")
      val c = HH (c, d, a, b, xj  7, 0w16, stow "0xf6bb4b60")
      val b = HH (b, c, d, a, xj 10, 0w23, stow "0xbebfbc70")
      val a = HH (a, b, c, d, xj 13, 0w4,  stow "0x289b7ec6")
      val d = HH (d, a, b, c, xj  0, 0w11, stow "0xeaa127fa")
      val c = HH (c, d, a, b, xj  3, 0w16, stow "0xd4ef3085")
      val b = HH (b, c, d, a, xj  6, 0w23, stow "0x04881d05")
      val a = HH (a, b, c, d, xj  9, 0w4,  stow "0xd9d4d039")
      val d = HH (d, a, b, c, xj 12, 0w11, stow "0xe6db99e5")
      val c = HH (c, d, a, b, xj 15, 0w16, stow "0x1fa27cf8")
      val b = HH (b, c, d, a, xj  2, 0w23, stow "0xc4ac5665")

      (* Round 4*)
      val a = II (a, b, c, d, xj  0, 0w6,  stow "0xf4292244")
      val d = II (d, a, b, c, xj  7, 0w10, stow "0x432aff97")
      val c = II (c, d, a, b, xj 14, 0w15, stow "0xab9423a7")
      val b = II (b, c, d, a, xj  5, 0w21, stow "0xfc93a039")
      val a = II (a, b, c, d, xj 12, 0w6,  stow "0x655b59c3")
      val d = II (d, a, b, c, xj  3, 0w10, stow "0x8f0ccc92")
      val c = II (c, d, a, b, xj 10, 0w15, stow "0xffeff47d")
      val b = II (b, c, d, a, xj  1, 0w21, stow "0x85845dd1")
      val a = II (a, b, c, d, xj  8, 0w6,  stow "0x6fa87e4f")
      val d = II (d, a, b, c, xj 15, 0w10, stow "0xfe2ce6e0")
      val c = II (c, d, a, b, xj  6, 0w15, stow "0xa3014314")
      val b = II (b, c, d, a, xj 13, 0w21, stow "0x4e0811a1")
      val a = II (a, b, c, d, xj  4, 0w6,  stow "0xf7537e82")
      val d = II (d, a, b, c, xj 11, 0w10, stow "0xbd3af235")
      val c = II (c, d, a, b, xj  2, 0w15, stow "0x2ad7d2bb")
      val b = II (b, c, d, a, xj  9, 0w21, stow "0xeb86d391")
    in
      (a + aa, b + bb, c + cc, d + dd)
    end

(* Does the main loop of Step 4 of the algorithm:
 * Execute transformations *)
fun md5_trans a b c d msg =
    let
      val len = size msg
      val msg = appendPad msg len
      val msg = appendLen msg len
      val len = size msg

      fun x j i =
          bToWord (String.sub (msg, j + (i*4)    ),
                   String.sub (msg, j + (i*4) + 1),
                   String.sub (msg, j + (i*4) + 2),
                   String.sub (msg, j + (i*4) + 3))

      fun md5_loop (a, b, c, d) j =
          if j = len
          then (a, b, c, d)
          else md5_loop (transformations (a, b, c, d) (x j)) (j + 64)

      val (a, b, c, d) = md5_loop (a, b, c, d) 0
    in
      implode (wToBit a @ wToBit b @ wToBit c @ wToBit d)
    end

(* To convert from binary to hex *)
val hexdigits = "0123456789ABCDEF"
fun bToHex msg =
    String.translate
        (fn n =>
            implode [String.sub (hexdigits, ord n div 16),
                     String.sub (hexdigits, ord n mod 16)]) msg

fun md5hash msg = md5_trans A B C D msg

fun md5 msg = bToHex (md5hash msg)
end

