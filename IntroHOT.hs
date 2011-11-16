-- * A Tagfull evaluator for simply-typed lambda-calculus
-- This example is borrowed from the introduction section
-- of the paper
-- * Emir Pa{\v s}ali{\'c} and Walid Taha and Tim Sheard
-- * Tagless Staged Interpreters for Typed Languages, ICFP2002.
-- It is discussed in detail in the tagless-final paper by
--   Jacques Carette, Oleg Kiselyov, and Chung-chieh Shan

module IntroHOT where

-- The language is simply typed lambda-calculus with booleans,
-- and de Bruijn encoding of variables.

data Var = VZ | VS Var			-- de Bruijn indices

data Exp = V Var 
	 | B Bool 			-- Boolean literal
	 | L Exp 			-- Abstraction
	 | A Exp Exp			-- Application

-- Lookup in the environment
lookp VZ (x:_) = x
lookp (VS v) (_:env) = lookp v env

-- Unsuccessful attempt to write the evaluator
{-
eval0 env (V v) = lookp v env
eval0 env (B b) = b
eval0 env (L e) = \x -> eval0 (x:env) e
eval0 env (A e1 e2) = (eval0 env e1) (eval0 env e2)
-}

--     The lambda expression `\ x -> eval0 (x : env) e' has one argument,
--     but its type `Bool' has none
--     In the expression: \ x -> eval0 (x : env) e
--     In the definition of `eval0':
--         eval0 env (L e) = \ x -> eval0 (x : env) e
-- what is the type of env?
-- What is the result of eval0?
-- Why the L-line exhibits the interpretive overhead?

-- * //
-- We have to introduce the universal type
data U = UB Bool | UA (U -> U)

instance Show U where
    show (UB x) = "UB " ++ show x
    show (UA _) = "UA <fun>"

-- Now we can write the evaluator
eval env (V v) = lookp v env
eval env (B b) = UB b
eval env (L e) = UA (\x -> eval (x:env) e)
eval env (A e1 e2) = case eval env e1 of
		      UA f -> f (eval env e2)
-- the inferred type
-- eval :: [U] -> Exp -> U

-- A sample term
ti1 = A (L (V VZ)) (B True)
ti1_eval = eval [] ti1
-- UB True
-- Note the tag UB!

-- * partial pattern match in the A clause
-- So, we can get stuck if we try to apply a boolean
ti2a = A (B True) (B False)
ti2a_eval = eval [] ti2a

-- * partial pattern match in lookp
-- So, we can get stuck if we try to evaluate an open term
ti2o = A (L (V (VS VZ))) (B True) 
ti2o_eval = eval [] ti2o

-- * tagging and untagging of the UA tag
-- tagging overhead, part of the interpretive overhead

-- * //
-- * But well-typed programs don't go wrong!
-- The terms ti2a and ti2o are ill-typed in the object language
-- If an object term is well-typed, it shall be
-- interpreted without any pattern-match failure.
-- So, how to communicate to the system that runs the interpreter 
-- that the object term is well-typed, so the pattern-match
-- code could be compiled efficiently, without any error-handling.

-- * Problem: algebraic data types Exp and Var express more terms that
-- * all well-typed terms in simply-typed lambda-calculus
-- * Run-time checks in eval become necessary
-- Because we can express ill-typed terms, we have all the run-time
-- checks in the form of type tags UA/UB and empty-list checks
-- in lookp

main = do
       print ti1_eval

