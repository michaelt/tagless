-- * Demonstrating `non-compositional', context-sensitive processing
-- * The initial style
-- * Flatten the additions

module FlatI where

import Intro1 hiding (main)
import PushNegI as Neg hiding (main)

-- Flatten the additions using the associativity
-- * (A + B) + R => A + (B + R)
-- Draw the trees for the former and the latter
-- The goal is to convert the addition tree to the right-skewed form
-- The transformation is assumed to be performed after the negation is
-- pushed down

-- Previously, expressions were constructed according to this grammar:
-- * General grammar of expressions
-- *     e ::= lit | neg e | add e e
-- *
-- * Restricted grammar now:
-- *     e ::= factor | add factor e
-- *     factor ::= lit | neg lit
-- Now, only integer literals can be negated, and only once.

-- It is an expression transformer

flata :: Exp -> Exp
flata e@Lit{} = e
flata e@Neg{} = e			-- assumed negations are pushed down
flata (Add (Add e1 e2) e3) = flata (Add e1 (Add e2 e3))
flata (Add e1 e2) = Add e1 (flata e2)

-- Why is this terminating?
-- The last two clauses express the lexicographic ordering
-- on left-depth, total depth.
-- Is this code correct?

norm :: Exp -> Exp
norm = flata . push_neg

-- Use our sample term
-- We make it a bit complex
ti3 = (Add ti1 (Neg (Neg ti1)))

ti3_view = view ti3
-- "((8 + (-(1 + 2))) + (-(-(8 + (-(1 + 2))))))"

ti3_eval = eval ti3
-- 10

-- The normalized expression can be evaluated with any interpreter

ti3_norm = norm ti3

ti3_norm_view = view ti3_norm
-- "(8 + ((-1) + ((-2) + (8 + ((-1) + (-2))))))"

-- The result of the standard evaluation (the `meaning') is preserved

ti3_norm_eval = eval ti3_norm
-- 10


main = do
       print ti3_view
       print ti3_eval
       print ti3_norm_view
       print ti3_norm_eval
       if ti3_eval == ti3_norm_eval then return ()
	  else error "Normalization"
