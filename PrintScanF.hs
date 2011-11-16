-- * Haskell98!

-- * The final view to the typed sprintf AND sscanf

module PrintScanF where

import Prelude hiding ((^))

-- This code defines a simple domain-specific language of string
-- patterns and demonstrates two interpreters of the language:
-- for building strings (sprintf) and parsing strings (sscanf).
-- This code thus solves the problem of typed printf/scanf sharing the
-- same format string, posed by Chung-chieh Shan.
-- This code presents scanf/printf interpreters in the final style;
-- it is thus the dual of the code in PrintScan.hs
-- September 2008.
-- See http://okmij.org/ftp/typed-formatting/

-- The typed sprintf problem has been investigated extensively: the first
-- solution was shown by Danvy; more solutions were proposed by Hinze and
-- Asai. The typed scanf problem received significantly less attention,
-- if any. It seems that the implementation of the typed sprintf and
-- sscanf sharing the same formatting specification has not been known.

-- We demonstrate that lambda-abstractions at the type level are
-- expressible already in the Hindley-Milner type system.

-- * Specification:
-- *  sprintf spec arg1 ... argn   ==> String
-- *  sscanf  input spec (\arg1 ... argn -> res)  ==> Maybe res
-- The typed sprintf takes the formatting specification and several
-- arguments and returns the formatted string. The types and the number
-- of arguments depend on the formatting specification. Conversely, the
-- typed sscanf parses a string according to the formatting
-- specification, passing parsed data to a consumer function. Again, the
-- number and the types of the arguments to the consumer depend on the
-- formatting specification. 

-- * Simple examples

tp1 = sprintf $ lit "Hello world"
-- "Hello world"
ts1 = sscanf "Hello world" (lit "Hello world")  ()
-- Just ()

tp2 = sprintf (lit "Hello " ^ lit "world" ^ char) '!'
-- "Hello world!"
ts2 = sscanf "Hello world!" (lit "Hello " ^ lit "world" ^ char) id
-- Just '!'

-- A formatting specification is built by connecting primitive
-- specifications (such as lit "string", int, char) with (^). We observe
-- that whereas 
--      sprintf $ lit "Hello world"
-- has the type String, 
--      sprintf $ lit "The value of " ^ char ^ lit " is " ^ int
-- has the type Char -> Int -> String. Likewise, the type of the consumer
-- of the values parsed by sscanf varies with the formatting specification.
-- The example of tp3 and ts3 demonstrates that sprintf and sscanf can
-- indeed use exactly the same formatting specification, which
-- is a first-class value.

-- * //
-- * Main idea
-- The formatting specification is a `type transformer', a functor.
-- *  Ralf Hinze: Functional Pearl: Formatting: a class act. 
-- *  JFP, 13(5):935-944, September 2003
-- int   ===> Int->
-- Examples: 
-- * sprintf (lit "xxx")     :: String
-- * sprintf int             :: Int -> String
-- * sprintf (char ^ int)    :: Char -> Int -> String
-- *
-- * sscanf inp (lit "xxx")  :: x - > Maybe x
-- * sscanf inp int          :: (Int -> x) -> Maybe x
-- * sscanf inp (char ^ int) :: (Char -> Int -> x) -> Maybe x

-- * //
-- Ralf Hinze representation of functors: type constructors
-- * Identity         data Id
-- * (x->)            data From x
-- * Composition      data C f x
-- Need interpretation

-- * //
-- * data F a b

-- * Identity         data Id         F a a
-- * (x->)            data From x     F a (x->a)
-- * Composition      data C f x      exercise
-- comp:: F a b -> F b c -> F a c

-- Emulating lambda in Prolog
-- Currying: (X,(Y,E)) <==> ((X,Y),E)


-- * //
-- * DSL for string patterns
class FormattingSpec repr where
    lit  :: String -> repr a a
    int  :: repr a (Int -> a)
    char :: repr a (Char -> a)
    fpp  :: PrinterParser b -> repr a (b -> a)
    (^)  :: repr b c -> repr a b -> repr a c
infixl 5 ^

-- Unit is to keep the type of fmt3 polymorphic and away from the
-- monomorphism restriction
fmt3 () = lit "The value of " ^ char ^ lit " is " ^ int

-- Printer/parsers (injection/projection pairs)
data PrinterParser a = PrinterParser (a -> String) (String -> Maybe (a,String))

fmt :: (FormattingSpec repr, Show b, Read b) => b -> repr a (b -> a)
fmt x = fpp showread


-- * //
-- * The interpreter for printf 

-- * The type of sprintf is exactly as we wanted!
-- From our examples
sprintf :: FPr String b -> b
sprintf (FPr fmt) = fmt id


-- It implements Asai's accumulator-less alternative to
-- Danvy's functional unparsing

newtype FPr a b = FPr ((String -> a) -> b)
-- Reminds you of something?
-- Right Kahn extension!

instance FormattingSpec FPr where
    lit str = FPr $ \k -> k str
    int     = FPr $ \k -> \x -> k (show x)
    char    = FPr $ \k -> \x -> k [x]
    fpp (PrinterParser pr _) = FPr $ \k -> \x -> k (pr x)
    (FPr a) ^ (FPr b)  = FPr $ \k -> a (\sa -> b (\sb -> k (sa ++ sb)))

tp3 = sprintf (fmt3 ()) 'x' 3
-- "The value of x is 3"

-- * //
-- * The interpreter for scanf

-- * The type is again what we expected
sscanf :: String -> FSc a b -> b -> Maybe a
sscanf inp (FSc fmt) f = maybe Nothing (Just . fst) $ fmt inp f

newtype FSc a b = FSc (String -> b -> Maybe (a,String))

instance FormattingSpec FSc where
    lit str = FSc $ \inp x -> 
		    maybe Nothing (\inp' -> Just (x,inp')) $ prefix str inp
    char    = FSc $ \inp f -> case inp of
		               (c:inp)  -> Just (f c,inp)
		               ""       -> Nothing
    fpp (PrinterParser _ pa) = FSc $ \inp f ->
	maybe Nothing (\(v,s) -> Just (f v,s)) $ pa inp
    int     = fpp showread
    (FSc a) ^ (FSc b) = FSc $ \inp f ->
	maybe Nothing (\(vb,inp') -> b inp' vb) $ a inp f


ts3 = sscanf "The value of x is 3" (fmt3 ()) (\c i -> (c,i))
-- Just ('x',3)


-- * Other interpreters are possible (to C-style strings)
-- One can easily build another interpreter, to convert a formatting
-- specification to a C-style formatting string


-- Tests



tp4 = sprintf (lit "abc" ^ int ^ lit "cde") 5
-- "abc5cde"
ts4 = sscanf "abc5cde" (lit "abc" ^ int ^ lit "cde") id
-- Just 5

-- The format specification is first-class. One can build format specification
-- incrementally
-- This is not the case with OCaml's printf/scanf (where the 
-- format specification has a weird typing and is not first class).
-- Unit is to keep the type of fmt3 polymorphic and away from the
-- monomorphism restriction
fmt50 () = lit "abc" ^ int ^ lit "cde" 
fmt5 () = fmt50 () ^ fmt (undefined::Float) ^ char
tp5 = sprintf (fmt5 ()) 5 15 'c'
-- "abc5cde15.0c"
ts5 = sscanf "abc5cde15.0c" (fmt5 ()) (\i f c -> (i,f,c))
-- Just (5,15.0,'c')


-- Utility functions

-- Primitive Printer/parsers
showread :: (Show a, Read a) => PrinterParser a
showread = PrinterParser show parse
 where
 parse s = case reads s of
	     [(v,s')] -> Just (v,s')
	     _        -> Nothing

-- A better prefixOf function
-- prefix patt str --> Just str'
--    if the String patt is the prefix of String str. The result str'
--    is str with patt removed
-- Otherwise, the result is Nothing

prefix :: String -> String -> Maybe String
prefix "" str = Just str
prefix (pc:pr) (sc:sr) | pc == sc = prefix pr sr
prefix _  _  = Nothing

main = do
       print tp1
       print ts1

       print tp2
       print ts2

       print tp3
       print ts3

       print tp4
       print ts4

       print tp5
       print ts5

