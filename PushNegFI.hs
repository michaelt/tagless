{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Demonstrating `non-compositional', context-sensitive processing
-- * The final style, via the intermediate data type.
-- This is cheating. But it does show the relationship between
-- initial and final. It also points out that everything we can
-- do with the data type, we can do in the final approach too -- albeit
-- with cheating in this case

module PushNegFI where

-- Explain the imports:
import Intro2 hiding (main)		-- The final representation of Exp

import Intro1 (Exp(..))			-- import the Exp data type
import qualified PushNegI as I		-- use the initial push_neg as it was

-- * //
-- We write the interpreter for final terms that produce initial, data type
-- terms

instance ExpSYM Exp where
    lit = Lit				-- nice symmetry between upper-and
    neg = Neg				-- lower case
    add = Add

initialize :: Exp -> Exp
initialize = id

-- * //
-- We write an evaluator for data type that produces final representation
-- The analogy with fold must be patent.

finalize :: ExpSYM repr => Exp -> repr	-- could have been inferred
finalize (Lit n) = lit n
finalize (Neg e) = neg (finalize e)
finalize (Add e1 e2) = add (finalize e1) (finalize e2)

-- * //
-- Now, push_neg in the final style is a mere composition
push_neg = finalize . I.push_neg . initialize

-- * Deforestation? Fusion laws?

-- Open research question: can the intermediate Exp data type be removed
-- by deforestation? Can we propose fusion laws to eliminate Exp?

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
       print PushNegFI.tf1_view
       print tf1_norm_view
       print tf1n_norm_view
       if tf1_norm_view == tf1nn_norm_view then return ()
	  else error "Double neg"
       print tf1nn_norm_view
       if eval tf1 == tf1_norm_eval then return ()
	  else error "Normalization"
       if eval tf1 == - tf1n_norm_eval then return ()
	  else error "Normalization"

