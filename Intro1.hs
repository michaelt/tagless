-- * Tagless Typed Interpreters, introduction

module Intro1 where

-- We would like to embed an (object) language whose expressions
-- look like
--     -(1 + 2)
-- *     8 + (- (1+2))
-- The expressions are built of integer literals, negation and addition.
-- The latter is one of our running example, please take note.

-- * Deep/initial embedding
-- The data type of expressions
data Exp = Lit Int  
         | Neg Exp 
         | Add Exp Exp

-- A sample expression: our first running example
ti1 = Add (Lit 8) (Neg (Add (Lit 1) (Lit 2)))

-- * //
-- The evaluator
-- It proceeds by case analysis on the expression
eval:: Exp -> Int
eval (Lit n)     = n
eval (Neg e)     = - eval e
eval (Add e1 e2) = eval e1 + eval e2


ti1_eval = eval ti1
-- 5

{-
data Exp where
  Lit :: Int -> Exp
  Neg :: Exp -> Exp
  Add :: Exp -> Exp -> Exp

type Wrap a =  a

-}
type Wrap a =  a
literal :: a -> Wrap a
literal a = a

negated :: Num a => Wrap a -> Wrap a
negated a = - a
-- * //
-- A different way to write the evaluator:
-- using the `constructor functions'

type Repr = Int

lit :: Int -> Repr
lit n = n

neg :: Repr -> Repr
neg e = - e

-- What is the inferred type for add? What type should we rather assign?
add e1 e2 = e1 + e2

-- Perhaps this already reminds someone of the denotational semantics.
-- More reminders to come.


-- Our sample expression in the final form:
-- I just downcased ti1 
tf1 = add (lit 8) (neg (add (lit 1) (lit 2)))
-- 5

-- * Shallow (metacircular) embedding (to be called final)
-- * //
-- But the datatype way (initial way) lets us `evaluate' ti1
-- in a different way: to pretty-print it

view:: Exp -> String
view (Lit n) = show n
view (Neg e) = "(-" ++ view e ++ ")"
view (Add e1 e2) = "(" ++ view e1 ++ " + " ++ view e2 ++ ")"

ti1_view = view ti1
-- "(8 + (-(1 + 2)))"

-- How can we evaluate tf1 differently? It seems that the evaluator
-- is hard-wired into tf1...
-- Indeed, the constructor functions lit, neg, and add all have
-- return type that is set to Int. The evaluator `view' returns a string.
-- So, at the very least we must find a way to parameterize the constructor
-- functions by the result type.

{-
main = do
       print ti1_eval
       print tf1
       print ti1_view
-}