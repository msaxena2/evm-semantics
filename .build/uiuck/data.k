// EVM Words
// =========

// EVM uses bounded 256 bit integer words, and sometimes also bytes (8 bit words).
// Here we provide the arithmetic of these words, as well as some data-structures
// over them. Both are implemented using K's `Int`.


requires "domains.k"

module EVM-DATA
    imports KRYPTO

    syntax KResult ::= Int


// Some important numbers for rounding to:


    syntax Int ::= "pow256" [function]
                 | "pow255" [function]
                 | "pow16"  [function]
 // ----------------------------------
    rule pow256 => 2 ^Int 256
    rule pow255 => 2 ^Int 255
    rule pow16  => 2 ^Int 16


// Primitives
// ----------

// Primitives provide the basic conversion from K's sorts `Int` and `Bool` to EVM's
// sort `Word`.

// -   `Int` is a subsort of `Word`.
// -   `chop` interperets an integer module $2^256$.


    syntax Word ::= Int | chop ( Word ) [function]
 // ----------------------------------------------
    rule chop( W:Int ) => W %Int pow256


// -   `bool2Word` interperets a `Bool` as a `Word`.
// -   `word2Bool` interperets a `Word` as a `Bool`.


    syntax Word ::= bool2Word ( Bool ) [function]
 // ---------------------------------------------
    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    syntax Bool ::= word2Bool ( Word ) [function]
 // ---------------------------------------------
    rule word2Bool( 0 ) => false
    rule word2Bool( W ) => true  requires W =/=K 0


// -   `#ifWord_#then_#else_#fi` provides a conditional in `Word` expressions.


    syntax Word ::= "#ifWord" Bool "#then" Word "#else" Word "#fi" [function]
 // -------------------------------------------------------------------------
    rule #ifWord true  #then W #else _ #fi => W
    rule #ifWord false #then _ #else W #fi => W


// -   `sgn` gives the twos-complement interperetation of the sign of a `Word`.
// -   `abs` gives the twos-complement interperetation of the magnitude of a
//     `Word`.


    syntax Int ::= sgn ( Word ) [function]
                 | abs ( Word ) [function]
 // --------------------------------------
    rule sgn(I:Int) => -1 requires I >=Int pow255
    rule sgn(I:Int) => 1  requires I <Int pow255

    rule abs(I:Int) => 0 -Word I requires sgn(I) ==K -1
    rule abs(I:Int) => I         requires sgn(I) ==K 1


// ### Symbolic Words

// -   `#symbolicWord` generates a fresh existentially-bound symbolic word.

// Note: Comment out this block (remove the `k` tag) if using RV K.


    syntax Word ::= "#symbolicWord" [function]
 // ------------------------------------------
    rule #symbolicWord => ?X:Int


// Arithmetic
// ----------

// -   `up/Int` performs integer division but rounds up instead of down.

// NOTE: Here, we choose to add `I2 -Int 1` to the numerator beforing doing the
// division to mimic the C++ implementation. You could alternatively calculate
// `I1 %Int I2`, then add one to the normal integer division afterward depending on
// the result.


    syntax Int ::= Int "up/Int" Int [function]
 // ------------------------------------------
    rule I1 up/Int 0  => 0
    rule I1 up/Int 1  => I1
    rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires I2 >Int 1


// -   `logNInt` returns the log base N (floored) of an integer.


    syntax Int ::= log2Int ( Int ) [function]
 // -----------------------------------------
    rule log2Int(1)     => 0
    rule log2Int(W:Int) => 1 +Int log2Int(W >>Int 1) requires W >Int 1

    syntax Int ::= log256Int ( Int ) [function]
 // -------------------------------------------
    rule log256Int(N:Int) => log2Int(N) /Int 8


// The corresponding `<op>Word` operations automatically perform the correct `Word`
// modulus.


    syntax Word ::= Word "+Word" Word [function]
                  | Word "*Word" Word [function]
                  | Word "-Word" Word [function]
                  | Word "/Word" Word [function]
                  | Word "%Word" Word [function]
 // --------------------------------------------
    rule W0:Int +Word W1:Int => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int => chop( (W0 +Int pow256) -Int W1 )
    rule W0:Int *Word W1:Int => chop( W0 *Int W1 )
    rule W0:Int /Word 0      => 0
    rule W0:Int /Word W1:Int => chop( W0 /Int W1 ) requires W1 =/=K 0
    rule W0:Int %Word 0      => 0
    rule W0:Int %Word W1:Int => chop( W0 %Int W1 ) requires W1 =/=K 0


// Care is needed for `^Word` to avoid big exponentiation.


    syntax Word ::= Word "^Word" Word [function]
 // --------------------------------------------
    rule W0:Int ^Word W1:Int => (W0 ^Word (W1 /Int 2)) ^Word 2  requires W1 >=Int pow16 andBool W1 %Int 2 ==Int 0
    rule W0:Int ^Word W1:Int => (W0 ^Word (W1 -Int 1)) *Word W0 requires W1 >=Int pow16 andBool W1 %Int 2 ==Int 1


// RV-K has a more efficient power-modulus operator.


    rule W0:Int ^Word W1:Int => (W0 ^Int W1) %Int pow256 requires W1 <Int pow16


// `/sWord` and `%sWord` give the signed interperetations of `/Word` and `%Word`.


    syntax Word ::= Word "/sWord" Word [function]
                  | Word "%sWord" Word [function]
 // ---------------------------------------------
    rule W0:Int /sWord W1:Int => #sgnInterp(sgn(W0) *Int sgn(W1) , abs(W0) /Word abs(W1))
    rule W0:Int %sWord W1:Int => #sgnInterp(sgn(W0)              , abs(W0) %Word abs(W1))

    syntax Word ::= #sgnInterp ( Word , Word ) [function]
 // -----------------------------------------------------
    rule #sgnInterp( 0  , W1 ) => 0
    rule #sgnInterp( W0 , W1 ) => W1         requires W0 >Int 0
    rule #sgnInterp( W0 , W1 ) => 0 -Word W1 requires W0 <Int 0


// Comparison Operators
// --------------------

// The `<op>Word` comparison operators automatically interperet the `Bool` as a
// `Word`.


    syntax Word ::= Word "<Word"  Word [function]
                  | Word ">Word"  Word [function]
                  | Word "<=Word" Word [function]
                  | Word ">=Word" Word [function]
                  | Word "==Word" Word [function]
 // ---------------------------------------------
    rule W0:Int <Word  W1:Int => 1 requires W0 <Int   W1
    rule W0:Int <Word  W1:Int => 0 requires W0 >=Int  W1
    rule W0:Int >Word  W1:Int => 1 requires W0 >Int   W1
    rule W0:Int >Word  W1:Int => 0 requires W0 <=Int  W1
    rule W0:Int <=Word W1:Int => 1 requires W0 <=Int  W1
    rule W0:Int <=Word W1:Int => 0 requires W0 >Int   W1
    rule W0:Int >=Word W1:Int => 1 requires W0 >=Int  W1
    rule W0:Int >=Word W1:Int => 0 requires W0 <Int   W1
    rule W0:Int ==Word W1:Int => 1 requires W0 ==Int  W1
    rule W0:Int ==Word W1:Int => 0 requires W0 =/=Int W1


// -   `s<Word` implements a less-than for `Word` (with signed interperetation).


    syntax Word ::= Word "s<Word" Word [function]
 // ---------------------------------------------
    rule W0:Int s<Word W1:Int => W0 <Word W1           requires sgn(W0) ==K 1  andBool sgn(W1) ==K 1
    rule W0:Int s<Word W1:Int => bool2Word(false)      requires sgn(W0) ==K 1  andBool sgn(W1) ==K -1
    rule W0:Int s<Word W1:Int => bool2Word(true)       requires sgn(W0) ==K -1 andBool sgn(W1) ==K 1
    rule W0:Int s<Word W1:Int => abs(W1) <Word abs(W0) requires sgn(W0) ==K -1 andBool sgn(W1) ==K -1


// Bitwise Operators
// -----------------

// Bitwise logical operators are lifted from the integer versions.


    syntax Word ::= "~Word" Word        [function]
                  | Word "|Word" Word   [function]
                  | Word "&Word" Word   [function]
                  | Word "xorWord" Word [function]
 // ----------------------------------------------
    rule ~Word W:Int           => chop( W xorInt (pow256 -Int 1) )
    rule W0:Int |Word   W1:Int => chop( W0 |Int W1 )
    rule W0:Int &Word   W1:Int => chop( W0 &Int W1 )
    rule W0:Int xorWord W1:Int => chop( W0 xorInt W1 )


// -   `bit` gets bit $N$ (0 being MSB).
// -   `byte` gets byte $N$ (0 being the MSB).


    syntax Word ::= bit  ( Word , Word ) [function]
                  | byte ( Word , Word ) [function]
 // -----------------------------------------------
    rule bit(N:Int, _)  => 0 requires N <Int 0 orBool N >=Int 256
    rule byte(N:Int, _) => 0 requires N <Int 0 orBool N >=Int 32

    rule bit(N:Int, W:Int)  => (W >>Int (255 -Int N)) %Int 2                            requires N >=Int 0 andBool N <Int 256
    rule byte(N:Int, W:Int) => (W >>Int (256 -Int (8 *Int (N +Int 1)))) %Int 256 requires N >=Int 0 andBool N <Int 32


// -   `#nBits` shifts in $N$ ones from the right.
// -   `#nBytes` shifts in $N$ bytes of ones from the right.
// -   `_<<Byte_` shifts an integer 8 bits to the left.


    syntax Int ::= #nBits  ( Int )  [function]
                 | #nBytes ( Int )  [function]
                 | Int "<<Byte" Int [function]
 // ------------------------------------------
    rule #nBits(N)  => (1 <<Int N) -Int 1  requires N >=Int 0
    rule #nBytes(N) => #nBits(N *Int 8)   requires N >=Int 0
    rule N <<Byte M => N <<Int (8 *Int M)


// -   `signextend(N, W)` sign-extends from byte $N$ of $W$ (0 being MSB).


    syntax Word ::= signextend( Word , Word ) [function]
 // ----------------------------------------------------
    rule signextend(N:Int, W:Int) => W requires N >=Int 32 orBool N <Int 0
    rule signextend(N:Int, W:Int) => chop( (#nBytes(31 -Int N) <<Byte (N +Int 1)) |Int W ) requires N <Int 32 andBool N >=Int 0 andBool         word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))
    rule signextend(N:Int, W:Int) => chop( #nBytes(N +Int 1)                      &Int W ) requires N <Int 32 andBool N >=Int 0 andBool notBool word2Bool(bit(256 -Int (8 *Int (N +Int 1)), W))


// -   `keccak` serves as a wrapper around the `Keccak256` in `KRYPTO`.


    syntax Word ::= keccak ( List ) [function]
 // ------------------------------------------
    rule keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS)))


// -   `#take(N , WS)` keeps the first $N$ elements of a `WordStack` (passing with
//     zeros as needed).
// -   `#drop(N , WS)` removes the first $N$ elements of a `WordStack`.


    syntax List ::= #take ( Word , List ) [function]
 // ------------------------------------------------
    rule #take(N, WS) => range(#padToWidthAfter(N, WS), 0, size(#padToWidthAfter(N, WS)) -Int N)

    syntax List ::= #drop ( Word , List ) [function]
 // ------------------------------------------------
    rule #drop(N, WS) => #if N >=Int size(WS) #then .List #else range(WS, N, 0) #fi


// -   `WS [ N := W ]` sets element $N$ of $WS$ to $W$ (padding with zeros
//     as needed).


    syntax List ::= List "[" Word ":=" Word "]" [function]
 // ------------------------------------------------------
    rule WS:List [ N := W ] => range(WS, 0, size(WS) -Int N) ListItem(W) range(WS, N +Int 1, 0)

    syntax List ::= List "[" Word ".." Word "]" [function]
 // ------------------------------------------------------
    rule WS [ START .. WIDTH ] => #if START >=Int size(WS) #then #padToWidthAfter(WIDTH, .List) #else range(#padToWidthAfter(START +Int WIDTH, WS), START, size(#padToWidthAfter(START +Int WIDTH, WS)) -Int START -Int WIDTH) #fi


// -   `#padToWidth(N, WS)` pads `WS` on the left with zeros until it is width `N`.
// -   `#padToWidthAfter(N, WS)` does the same but pads zeros on the right.


    syntax List ::= #padToWidth ( Int , List ) [function]
 // -----------------------------------------------------
    rule #padToWidth(N, WS) => WS                             requires notBool size(WS) <Int N
    rule #padToWidth(N, WS) => #padToWidth(N, ListItem(0) WS) requires size(WS) <Int N

    syntax List ::= #padToWidthAfter ( Int , List ) [function]
 // ----------------------------------------------------------
    rule #padToWidthAfter(N, WS) => WS                                  requires notBool size(WS) <Int N
    rule #padToWidthAfter(N, WS) => #padToWidthAfter(N, WS ListItem(0)) requires size(WS) <Int N


// Data Structures
// ===============

// Several data-structures and operations over `Word` are useful to have around.

// Byte Arrays
// -----------

// The local memory of execution is a byte-array (instead of a word-array).

// -   `#asWord` will interperet a stack of bytes as a single word (with
//     MSB first).
// -   `#asByteStack` will split a single word up into a `List` where each word is
//     a byte wide.


    syntax Word ::= #asWord ( List ) [function]
 // -------------------------------------------
    rule #asWord( .List )                        => 0
    rule #asWord( ListItem(W) )                  => W
    rule #asWord( ListItem(W0) ListItem(W1) WS ) => #asWord(ListItem((W0 *Word 256) +Word W1) WS)

    syntax List ::= #asByteStack ( Word )        [function]
                  | #asByteStack ( Word , List ) [function, klabel(#asByteStackAux)]
 // --------------------------------------------------------------------------------
    rule #asByteStack( W ) => #asByteStack( W , .List )
    rule #asByteStack( 0 , WS ) => WS
    rule #asByteStack( W , WS ) => #asByteStack( W /Int 256 , ListItem(W %Int 256) WS ) requires W =/=K 0


// Addresses
// ---------

// -   `#addr` turns an Ethereum word into the corresponding Ethereum address
//     (160 LSB).


    syntax Word ::= #addr ( Word ) [function]
 // -----------------------------------------
    rule #addr(W) => W %Word (2 ^Word 160)


// -   `#newAddr` computes the address of a new account given the address and nonce
//     of the creating account.


    syntax Word ::= #newAddr ( Word , Word ) [function]
 // ---------------------------------------------------
    rule #newAddr(ACCT, NONCE) => #addr(#parseHexWord(Keccak256(#rlpEncodeLength(#rlpEncodeWord(ACCT) +String #rlpEncodeWord(NONCE), 192))))

    syntax String ::= #rlpEncodeLength ( String , Int )          [function]
                    | #rlpEncodeLength ( String , Int , String ) [function, klabel(#rlpEncodeLengthAux)]
                    | #rlpEncodeWord ( Word )                    [function]
 // -----------------------------------------------------------------------
    rule #rlpEncodeWord(0) => "\x80"
    rule #rlpEncodeWord(WORD) => chrChar(WORD) requires WORD >Int 0 andBool WORD <Int 128
    rule #rlpEncodeWord(WORD) => #rlpEncodeLength(#unparseByteStack(#asByteStack(WORD)), 128) requires WORD >=Int 128
    rule #rlpEncodeLength(STR, OFFSET) => chrChar(lengthString(STR) +Int OFFSET) +String STR requires lengthString(STR) <Int 56
    rule #rlpEncodeLength(STR, OFFSET) => #rlpEncodeLength(STR, OFFSET, #unparseByteStack(#asByteStack(lengthString(STR)))) requires lengthString(STR) >=Int 56
    rule #rlpEncodeLength(STR, OFFSET, BL) => chrChar(lengthString(BL) +Int OFFSET +Int 55) +String BL +String STR


// Word Map
// --------

// Most of EVM data is held in finite maps. We are using the polymorphic `Map` sort
// for these word maps.

// -   `WM [ N := WS ]` assigns a contiguous chunk of $WM$ to $WS$ starting at
//     position $W$.
// -   `#asMapWordStack` converts a `List` to a `Map`.
// -   `#range(M, START, WIDTH)` reads off $WIDTH$ elements from $WM$ beginning at
//     position $START$ (padding with zeros as needed).


    syntax Map ::= Map "[" Word ":=" List "]" [function]
 // ----------------------------------------------------
    rule WM [ N := .List          ] => WM
    rule WM [ N := ListItem(W) WS ] => (WM [ N <- W ]) [ N +Word 1 := WS ]

    syntax Map ::= #asMapWordStack ( List ) [function]
 // --------------------------------------------------
    rule #asMapWordStack(WS:List) => .Map [ 0 := WS ]

    syntax List ::= #range ( Map , Word , Word )       [function]
    syntax List ::= #range ( Map , Word , Word , List) [function, klabel(#rangeAux)]
 // --------------------------------------------------------------------------------
    rule #range(WM, START:Int, WIDTH:Int) => #range(WM, START +Int WIDTH -Int 1, WIDTH, .List)
    rule #range(WM,           END:Int, 0,         WS) => WS
    rule #range(WM,           END:Int, WIDTH:Int, WS) => #range(WM, END -Int 1, WIDTH -Int 1, ListItem(0) WS) requires (WIDTH >Int 0) andBool notBool END in_keys(WM)
    rule #range(END |-> W WM, END:Int, WIDTH:Int, WS) => #range(WM, END -Int 1, WIDTH -Int 1, ListItem(W) WS) requires (WIDTH >Int 0)


// Parsing/Unparsing
// =================

// The EVM test-sets are represented in JSON format with hex-encoding of the data
// and programs. Here we provide some standard parser/unparser functions for that
// format.

// JSON
// ----

// Writing a JSON parser in K takes 6 lines.


    syntax JSONList ::= List{JSON,","}
    syntax JSONKey  ::= String | Word
    syntax JSON     ::= String
                      | JSONKey ":" JSON
                      | "{" JSONList "}"
                      | "[" JSONList "]"
 // ------------------------------------


// Parsing
// -------

// These parsers can interperet hex-encoded strings as `Word`s, `List`s, and
// `Map`s.

// -   `#parseHexWord` interperets a string as a single hex-encoded `Word`.
// -   `#parseHexBytes` interperets a string as a stack of bytes.
// -   `#parseByteStack` interperets a string as a stack of bytes, but makes sure
//     to remove the leading "0x".
// -   `#parseWordStack` interperets a JSON list as a stack of `Word`.
// -   `#parseMap` interperets a JSON key/value object as a map from `Word` to
//     `Word`.
// -   `#parseAddr` interperets a string as a 160 bit hex-endcoded address.


    syntax Word ::= #parseHexWord ( String ) [function]
                  | #parseWord    ( String ) [function]
 // ---------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0
    rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
    rule #parseWord(S)  => String2Int(S) [owise]

    syntax List ::= #parseHexBytes  ( String ) [function]
                  | #parseByteStack ( String ) [function]
 // -----------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))
    rule #parseHexBytes("") => .List
    rule #parseHexBytes(S)  => ListItem(#parseHexWord(substrString(S, 0, 2))) #parseHexBytes(substrString(S, 2, lengthString(S))) requires lengthString(S) >=Int 2

    syntax List ::= #parseWordStack ( JSON ) [function]
 // ---------------------------------------------------
    rule #parseWordStack( [ .JSONList ] )            => .List
    rule #parseWordStack( [ (WORD:String) , REST ] ) => ListItem(#parseHexWord(WORD)) #parseWordStack( [ REST ] )

    syntax Map ::= #parseMap ( JSON ) [function]
 // --------------------------------------------
    rule #parseMap( { .JSONList                   } ) => .Map
    rule #parseMap( { _   : (VALUE:String) , REST } ) => #parseMap({ REST })                                                requires #parseHexWord(VALUE) ==K 0
    rule #parseMap( { KEY : (VALUE:String) , REST } ) => #parseMap({ REST }) [ #parseHexWord(KEY) <- #parseHexWord(VALUE) ] requires #parseHexWord(VALUE) =/=K 0

    syntax Word ::= #parseAddr ( String ) [function]
 // ------------------------------------------------
    rule #parseAddr(S) => #addr(#parseHexWord(S))


// Unparsing
// ---------

// We need to interperet a `List` as a `String` again so that we can call
// `Keccak256` on it from `KRYPTO`.

// -   `#unparseByteStack` turns a stack of bytes (as a `List`) into a `String`.
// -   `#padByte` ensures that the `String` interperetation of a `Word` is
//     wide enough.


    syntax String ::= #unparseByteStack ( List ) [function]
 // -------------------------------------------------------
    rule #unparseByteStack( .List ) => ""
    rule #unparseByteStack( ListItem(W:Int) WS ) => chrChar(W %Int 256) +String #unparseByteStack(WS)

    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1
endmodule

