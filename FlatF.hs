{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Demonstrating `non-compositional', context-sensitive processing
-- * The final style
-- * Flatten the additions

module FlatF where

import Intro2 hiding (main)
import PushNegF as Neg hiding (Ctx) -- (main,Ctx)

-- We are going to write flata as an interpreter.
-- After all, that's all we can do with an expression in a final form.

-- * The nested pattern-matching establishes a context:
-- * flata :: Exp -> Exp
-- * flata e@Lit{} = e
-- * flata e@Neg{} = e
-- * flata (Add (Add e1 e2) e3) = flata (Add e1 (Add e2 e3))
-- * flata (Add e1 e2) = Add e1 (flata e2)

-- The processing is slightly different from push_neg, because we repeatedly
-- process the transformed expression (the last-but one clause)


-- * //
-- So, we define the context
data Ctx e = CtxNone | CtxAdd (Ctx e -> e)
-- CtxAdd e3 represents a context of adding e3 _to the right_ of
-- the expression in focus.

instance ExpSYM repr => ExpSYM (Ctx repr -> repr) where
    lit n CtxNone    = lit n
    lit n (CtxAdd e) = add (lit n) (e CtxNone)
    neg e CtxNone    = neg (e CtxNone)
    neg e (CtxAdd e3)= add (neg (e CtxNone)) (e3 CtxNone)
    add e1 e2 CtxNone = e1 (CtxAdd e2)
    add e1 e2 (CtxAdd e3) = e1 (CtxAdd (add e2 e3))

-- Keep in mind the processing is done bottom-up!

-- A general approach is to use continuations (or monads), 
-- or to encode the Ctx with zippers 
-- (the defunctionalized continuations, in the present
-- case).
-- The Ctx data type above is tuned to the present example,
-- keeping only the data we need (e.g., we aren't interested
-- in the context of Neg or of the addition on the left, 
-- and so we don't represent these cases in Ctx).


-- Exercise: there are several clauses where lit, neg, or add
-- appears on both sides of the definition. 
-- In which clause add is being used recursively?


-- The `interpreter' for flattening
flata :: (Ctx repr -> repr) -> repr
flata e = e CtxNone

norm = flata . Neg.push_neg

-- Use our sample term
-- We make it a bit complex
tf3 = (add tf1 (neg (neg tf1)))

tf3_view = view tf3
-- "((8 + (-(1 + 2))) + (-(-(8 + (-(1 + 2))))))"

tf3_eval = eval tf3
-- 10

-- The normalized expression can be evaluated with any interpreter

tf3_norm = norm tf3

tf3_norm_view = view tf3_norm
-- "(8 + ((-1) + ((-2) + (8 + ((-1) + (-2))))))"

-- The result of the standard evaluation (the `meaning') is preserved

tf3_norm_eval = eval tf3_norm
-- 10
{-
main = do
       print tf3_view
       print tf3_eval
       print tf3_norm_view
       print tf3_norm_eval
       if tf3_eval == tf3_norm_eval then return ()
	  else error "Normalization"
-}