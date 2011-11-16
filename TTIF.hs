{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Relating initial and final representations

module TTIF where

import TTF as F hiding (main)	-- The final embedding

-- * Initial embedding of our language, in HOAS
-- * (superset of the running example in Xi, Chen and Chen (POPL2003))
-- In the latter paper, the tagless interpretation of the
-- language was the motivation for GADT.

-- The initial embedding is not-extensible.
-- The Var operation is used only during evaluation.
-- Var corresponds to a CSP value in MetaOCaml or 
-- HOASLift in Xi, Chen and Chen (POPL2003)
-- The parameter h is the `hypothetical environment':
-- h t is the type of an environment `cell' holding a value of the type t.

data IR h t where
    INT  :: Int  -> IR h Int
    BOOL :: Bool -> IR h Bool

    Add  :: IR h Int -> IR h Int -> IR h Int
    Mul  :: IR h Int -> IR h Int -> IR h Int
    Leq  :: IR h Int -> IR h Int -> IR h Bool
    IF   :: IR h Bool -> IR h t -> IR h t -> IR h t

    Var  :: h t -> IR h t
    Lam  :: (IR h t1 -> IR h t2) -> IR h (t1->t2)
    App  :: IR h (t1->t2) -> IR h t1  -> IR h t2
    Fix  :: (IR h t -> IR h t) -> IR h t


-- * Sample terms and their inferred types
-- Compared to the terms in the final embedding, the initial
-- embedding terms below look capitalized (which is what I did in Emacs)

ti1 = Add (INT 1) (INT 2)
-- ti1 :: IR h Int
-- * th1 :: (Symantics repr) => repr Int

ti2 = Lam (\x -> Add x x)
-- ti2 :: IR h (Int -> Int)
-- th2 :: (Symantics repr) => repr (Int -> Int)

ti3 = Lam (\x -> Add (App x (INT 1)) (INT 2))
-- ti3 :: IR h ((Int -> Int) -> Int)
-- th3 :: (Symantics repr) => repr ((Int -> Int) -> Int)


tipow  = Lam (\x -> Fix (\self -> Lam (\n ->
                        IF (Leq n (INT 0)) (INT 1)
                            (Mul x (App self (Add n (INT (-1))))))))
-- tipow :: IR h (Int -> Int -> Int)
-- * tpow :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) =>
-- *       repr (Int -> Int -> Int)

tipow7 = Lam (\x -> App (App tipow x) (INT 7))
tipow72 = App tipow7 (INT 2)
-- tipow72 :: IR h Int
-- tpow72 :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) => 
-- repr Int

-- * //
-- * Initial evaluator

-- It is total (modulo potential non-termination in fix)
-- No exceptions are to be raised, and no pattern-match failure
-- may occur. All pattern-matching is _syntactically_, patently complete.
-- We use the same R as in TTF.hs 

evalI :: IR R t -> t
evalI (INT n)   = n
evalI (BOOL n)  = n
evalI (Add e1 e2) = evalI e1 + evalI e2
evalI (Mul e1 e2) = evalI e1 * evalI e2
evalI (Leq e1 e2) = evalI e1 <= evalI e2
evalI (IF be et ee) = if (evalI be) then evalI et else evalI ee
evalI (Var v) = unR v
evalI (Lam b) = \x -> evalI (b . Var . R $ x)
evalI (App e1 e2) = (evalI e1) (evalI e2)
evalI (Fix f) = evalI (f (Fix f))

ti1_eval = evalI ti1
-- 3

ti2_eval = evalI ti2
-- ti2_eval :: Int -> Int
-- ti2_eval is a function, can't be shown, but can be applied
ti2_eval' = ti2_eval 21
-- 42

ti3_eval = evalI ti3
-- ti3_eval :: (Int -> Int) -> Int

tipow72_eval = evalI tipow72
-- 128

-- * //
-- * Initial viewer (another evaluator)

-- The code essentially the same as the final one:
-- unS is replaced by viewI'

viewI' :: IR S t -> VarCounter -> String
viewI' (INT x)  = const $ show x
viewI' (BOOL x) = const $ show x
viewI' (Add e1 e2) = \h -> 
      "(" ++ viewI' e1 h ++ "+" ++ viewI' e2 h ++ ")"
viewI' (Mul e1 e2) = \h -> 
      "(" ++ viewI' e1 h ++ "*" ++ viewI' e2 h ++ ")"
viewI' (Leq e1 e2) = \h -> 
      "(" ++ viewI' e1 h ++ "<=" ++ viewI' e2 h ++ ")"
viewI' (IF be et ee) = \h -> 
       unwords["(if", viewI' be h, "then", viewI' et h, 
	       "else", viewI' ee h,")"]

viewI' (Var x) = unS x
viewI' (Lam e) = \h ->
       let x = "x" ++ show h
       in "(\\" ++ x ++ " -> " ++ 
            viewI' (e (Var . S $ const x)) (succ h) ++ ")"
viewI' (App e1 e2) = \h -> 
      "(" ++ viewI' e1 h ++ " " ++ viewI' e2 h ++ ")"
viewI' (Fix e) = \h ->
       let self = "self" ++ show h
       in "(fix " ++ self ++ "." ++ 
            viewI' (e (Var . S $ const self)) (succ h) ++ ")"

viewI e = viewI' e 0

ti1_view = viewI ti1
-- "(1+2)"

ti2_view = viewI ti2
-- "(\\x0 -> (x0+x0))"

ti3_view = viewI ti3
-- "(\\x0 -> ((x0 1)+2))"

tipow_view = viewI tipow
-- "(\\x0 -> (fix self1.(\\x2 -> 
--              (if (x2<=0) then 1 else (x0*(self1 (x2+-1))) ))))"

-- * This is all very similar to the final approach
-- * The same guarantees
-- No pattern-matching failure, only closed terms can be evaluated
-- The reason is that GADT IR encodes all and only well-typed terms
-- of the object language.
-- * IR is not extensible though
-- Because both initial and final embedding encode all and only
-- well-typed object terms, one may wonder if the two embeddings
-- may be related.

-- * //
-- * Relating Initial and Final Tagless representations

instance Symantics (IR h) where
    int  = INT
    add  = Add

    lam  = Lam
    app  = App

instance MulSYM (IR h) where
    mul  = Mul

instance BoolSYM (IR h) where
    bool = BOOL
    leq  = Leq
    if_  = IF

instance FixSYM (IR h) where
    fix  = Fix

-- * Looks like the identity, doesn't it?

-- * //
-- * From Final to Initial

f2i :: IR h t -> IR h t
f2i = id 

-- It does look like the identity


-- Conversion of sample terms

ti2' = f2i F.th2
-- Now we can evaluate it using different initial interpreters

ti2'_eval = evalI ti2'
-- ti2'_eval :: Int -> Int

ti2'_eval' = ti2'_eval 21
-- 42

ti2'_view = viewI ti2'
--"(\\x0 -> (x0+x0))"

-- The same for the power example
tipow72' = f2i F.tpow72

tipow72'_eval = evalI tipow72'
-- 128

tipow72'_view = viewI tipow72'
-- "((\\x0 -> (((\\x1 -> 
--      (fix self2.(\\x3 -> (if (x3<=0) then 1 else (x1*(self2 (x3+-1))) ))))
--   x0) 7)) 2)"


-- * //
-- * From Initial to Final

i2f :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) => 
       IR repr t -> repr t
i2f (INT x)  = int x
i2f (BOOL x) = bool x
i2f (Add e1 e2) = add (i2f e1) (i2f e2)
i2f (Mul e1 e2) = mul (i2f e1) (i2f e2)
i2f (Leq e1 e2) = leq (i2f e1) (i2f e2)
i2f (IF be et ee) = if_ (i2f be) (i2f et) (i2f ee)
i2f (Var v) = v				-- polymorphic lift
i2f (Lam e) = lam(\x -> i2f (e (Var x)))
i2f (App e1 e2) = app (i2f e1) (i2f e2)
i2f (Fix e) = fix(\x -> i2f (e (Var x)))

-- Convert sample terms

tf2' = i2f ti2
-- tf2' :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) =>
--      repr (Int -> Int)

-- Now we can evaluate it using different final interpreters

tf2'_eval = F.eval tf2'
-- tf2'_eval :: Int -> Int

tf2'_eval' = tf2'_eval 21
-- 42

tf2'_view = F.view tf2'
-- "(\\x0 -> (x0+x0))"

-- The same for the power term

tfpow72' = i2f tipow72

tfpow72'_eval = F.eval tfpow72'
-- 128

tfpow72'_view = F.view tfpow72'
-- the same as tipow72'_view

-- * //
-- * Verifying Initial -> Final -> Initial
-- * ifi :: IR (IR h) t -> IR h t
ifi ir = f2i . i2f $ ir

tipow72'_eval'' = evalI . ifi $ tipow72
-- 128

tipow72'_view'' = viewI . ifi $ tipow72

-- * Verifying Final -> Initial -> Final

fif fr = i2f . f2i $ fr
-- fif :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) =>
--      IR repr t -> repr t

tfpow72'_eval'' = F.eval . fif $ F.tpow72
-- 128

tfpow72'_view'' = F.view . fif $ F.tpow72

-- * Relation between initial and final is a bijection

main = do
       print ti1_eval
       print ti2_eval'
       print tipow72_eval

       print ti1_view
       print ti2_view
       print ti3_view
       print tipow_view

       print ti2'_eval'
       print tipow72'_eval
       print ti2'_view
       print tipow72'_view

       print tf2'_eval'
       print tfpow72'_eval
       print tf2'_view
       print tfpow72'_view

       print tipow72'_eval''
       print tipow72'_view''

       print tfpow72'_eval''
       print tfpow72'_view''

