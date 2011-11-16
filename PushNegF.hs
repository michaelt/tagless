{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Demonstrating `non-compositional', context-sensitive processing
-- * The final style

module PushNegF where

import Intro2 hiding (main)
import qualified Data.DList as D
import Data.DList (DList(..))
tfdl1_view = view tfdl1
-- When I first mentioned the initial and final styles in passing
-- in July 2009 in Oxford, one Oxford professor said:
-- ``Isn't it bloody obvious that you can't pattern-match in the final
-- style?''
-- The answer: it isn't bloody and it isn't obvious and it is not
-- impossible to pattern-match in the final style.

-- Pushing negation down
-- We are going to write push_neg as an interpreter.
-- After all, that's all we can do with an expression in a final form.

-- * The nested pattern-matching establishes a context:
-- * push_neg :: Exp -> Exp
-- * push_neg e@Lit{} = e
-- * push_neg e@(Neg (Lit _)) = e
-- * push_neg (Neg (Neg e)) = push_neg e
-- * push_neg (Neg (Add e1 e2)) = Add (push_neg (Neg e1)) (push_neg (Neg e2))
-- * push_neg (Add e1 e2) = Add (push_neg e1) (push_neg e2)

-- * //
-- So, we define the context
data Ctx = Pos | Neg


-- * Tagless transformer
-- We transform one interpreter into another
instance ExpSYM repr => ExpSYM (Ctx -> repr) where
    lit n Pos = lit n
    lit n Neg = neg (lit n)
    neg e Pos = e Neg
    neg e Neg = e Pos
    add e1 e2 ctx = add (e1 ctx) (e2 ctx) -- homomorhism

-- On the first line, there are two occurrences of lit.
-- But those two lit belong to different interpreters!
-- The observation holds for all other lines.

-- The transformation here seems more insightful than that in
-- PushNegI.hs: we see that with respect to |add|, the transformation
-- is just the homomorphism.

-- The `interpreter' for pushing the negation down
push_neg e = e Pos

-- * //
-- To remind, here is our sample term
tf1_view = view tf1
-- "(8 + (-(1 + 2)))"


tf1_norm = push_neg tf1

-- The new expression can be evaluated with any interpreter
tf1_norm_view = view tf1_norm
-- "(8 + ((-1) + (-2)))"
-- The result of the standard evaluation (the `meaning') is preserved
tf1_norm_eval = eval tf1_norm
-- 5

-- Add an extra negation
tf1n_norm = push_neg (neg tf1)

-- see the result
tf1n_norm_view = view tf1n_norm
-- "((-8) + (1 + 2))"
tf1n_norm_eval = eval tf1n_norm
-- -5

-- Negate the already negated term
tf1nn_norm = push_neg (neg tf1n_norm)
tf1nn_norm_view = view tf1nn_norm
-- "(8 + ((-1) + (-2)))"

main = do
       print PushNegF.tf1_view
       print tf1_norm_view
       print tf1n_norm_view
       if tf1_norm_view == tf1nn_norm_view then return ()
	  else error "Double neg"
       print tf1nn_norm_view
       if eval tf1 == tf1_norm_eval then return ()
	  else error "Normalization"
       if eval tf1 == - tf1n_norm_eval then return ()
	  else error "Normalization"



