-- * Demonstrating `non-compositional', context-sensitive processing
-- * The initial style

module PushNegI where

-- * Compositionality
--    The meaning of a complex expression is determined by its
--    structure and the meanings of its constituents.
--    http://plato.stanford.edu/entries/compositionality/
-- The epitome:
--        eval (Add e1 e2) = eval e1 + eval e2
--
--    - Evaluators and other interpreters are compositional
--    - Denotational semantics must be compositional
--    - Compositionality is modularity
--    - Compositionality is context-insensitivity
--    - Bottom-up reconstruction of meaning
--    - Compositional processing is `fold'
--
--  The final approach embodies `fold'
--
-- Optimization and other such program transformations give many
-- examples of apparently non-compositional processing

import Intro1 hiding (main)


-- * Pushing the negation down
-- Previously, expressions were constructed according to this grammar:
-- * General grammar of expressions
-- *     e ::= lit | neg e | add e e
-- *
-- * Restricted grammar:
-- *     e ::= factor | add e e
-- *     factor ::= lit | neg lit
-- Now, only integer literals can be negated, and only once.


-- * //
-- We don't compute the value of the expression. Rather, we are doing
-- a _symbolic_ transformation: transforming an expression into a different
-- expression, which is equivalent with respect to some set of laws.

-- * push_neg is an expression transformer

push_neg :: Exp -> Exp
push_neg e@Lit{} = e
push_neg e@(Neg (Lit _)) = e
push_neg (Neg (Neg e)) = push_neg e
push_neg (Neg (Add e1 e2)) = Add (push_neg (Neg e1)) (push_neg (Neg e2))
push_neg (Add e1 e2) = Add (push_neg e1) (push_neg e2)

-- The nested pattern-match betrays context-sensitivity

-- To remind, here is our sample term
ti1_view = view ti1
-- "(8 + (-(1 + 2)))"

ti1_norm = push_neg ti1

-- The new expression can be evaluated with any interpreter
ti1_norm_view = view ti1_norm
-- "(8 + ((-1) + (-2)))"

-- The result of the standard evaluation (the `meaning') is preserved
ti1_norm_eval = eval ti1_norm
-- 5

-- Add an extra negation
ti1n_norm = push_neg (Neg ti1)

-- see the result and its value
ti1n_norm_view = view ti1n_norm
-- "((-8) + (1 + 2))"
ti1n_norm_eval = eval ti1n_norm
-- -5

-- Negate the already negated term
ti1nn_norm = push_neg (Neg ti1n_norm)
ti1nn_norm_view = view ti1nn_norm
-- "(8 + ((-1) + (-2)))"

main = do
       print PushNegI.ti1_view
       print ti1_norm_view
       print ti1n_norm_view
       if ti1_norm_view == ti1nn_norm_view then return ()
	  else error "Double neg"
       if eval ti1 == ti1_norm_eval then return ()
	  else error "Normalization"
       if eval ti1 == - ti1n_norm_eval then return ()
	  else error "Normalization"
       print ti1nn_norm_view
       

--  LocalWords:  compositionality
