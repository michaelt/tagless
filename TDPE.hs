-- Essentially Haskell98!
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Type-directed partial evaluation
-- * Olivier Danvy, POPL96
-- * http://www.brics.dk/~danvy/tdpe-ln.pdf

module TDPE where

import TTF hiding (main)		-- HOAS Symantics

-- * ``black-box'' functions, _compiled_
import ToTDPE


-- * //
-- * Demo first
-- * bbf1 and bbf2 are imported from the _compiled_ module ToTDPE
-- We can see their types
-- TDPE> :t bbf1
-- bbf1 :: t -> t1 -> t
-- TDPE> :t bbf2
-- bbf2 :: (c -> c) -> c -> c
-- Can you tell what they are? Especially bbf2?
-- * It would be great to have a function a -> repr a

-- * //
-- * Deriving reify_t :: t -> repr t
-- We call this `magic' function reify. It is actually a family of
-- functions, indexed by types.
-- * Why the name `reify'?
-- We convert from a Haskell value of the type t to an object
-- _representing_ that value of type t.

-- * Start with reify_aa :: (a -> a) -> repr (a -> a)
-- Here, we convert from a metalanguage function (a->a) (`the thing')
-- to an object (EDSL) function repr (a->a). The latter is also a Haskell
-- value, which represents `the thing.'
-- In other words, we take an `abstract', or opaque function (a->a)
-- (which we can't print, for example) and produce an object (repr (a->a))
-- that we can view. In general, `reify' means representing an abstract
-- concept in terms of a concrete object a value.

-- We take as an input a _polymorphic_ Haskell function of the principal
-- type a->a. The input function also has the instantiated type
-- repr a -> repr a, right?
-- So, the real type of reify_aa is 
--    reify_aa :: (repr a -> repr a) -> repr (a->a)
-- Have we seen a function of that type already?
-- We thus obtain reify_aa = lam

-- * //
-- * Deriving reify_aabb :: (a->a)->(b->b) -> repr ((a->a)->(b->b))
-- Let us overlook a bit silly type of the term
-- The input function can be instantiated: we substitute (repr a) for a
-- and (repr b) for b. So, we need to convert
--    (repr a -> repr a) -> (repr b ->  repr b)
-- to repr ((a->a)->(b->b)).
-- The desired term has the form repr (t1->t2). There is only one way
-- to construct a term of that type, use lam. We write
-- reify_aabb f = lam (\x -> ???)
-- where x must have the type (repr (a->a)) and ??? must have the type
-- (repr (b->b)).
-- Recall, that f, the argument to reify_aabb has the type
--   (repr a -> repr a) -> (repr b ->  repr b)
-- Here is our plan: take x and somehow convert it to a term
-- of the type (repr a -> repr a). Pass the result to the function f,
-- obtaining a term of the type (repr b -> repr b).
-- We know how to convert that to (repr (b->b)): we apply reify_bb.
-- To carry out our plan, we need the function reflect:

-- * //
-- * We need reflect_aa :: repr (a->a) -> (repr a -> repr a)
-- It too is a family of functions, indexed by type. It is in a sense
-- the `inverse' of reify. We will talk about that sense later.
-- It takes an object _representing_ the true Haskell function, and
-- produces the _represented_ thing, the true Haskell function.
-- Have we already seen the function of that type? the `inverse' of lam?

-- Our final result:
-- reflect_aa = app
-- reify_aabb f = lam (\x -> reify_bb (f (reflect_aa x)))
-- What is reflect_aabb? Anyone?

-- * //
-- * We build reify_t and reflect_t together and inductively.

data RR repr meta obj = RR{reify   :: meta -> repr obj,
			   reflect :: repr obj -> meta}

-- * The base of induction (reify/reflect for base types)
base :: RR repr (repr a) a
base = RR{reify = id, reflect = id}

-- * The inductive case
infixr 8 -->				-- arrow constructor for RR

(-->) :: Symantics repr =>
         RR repr m1 o1 -> RR repr m2 o2 -> RR repr (m1 -> m2) (o1 -> o2)
r1 --> r2 = RR{reify   = \m -> lam (reify r2 . m . reflect r1),
	       reflect = \o -> reflect r2 . app o . reify r1}

-- reflect looks like eta-expansion: \x -> app o x,
-- with intervening reify/reflect and the change of levels

-- * //
-- * Examples

-- We come back to the original question: what are bbf1 and bbf2?

tb1 = reify (base --> base --> base) bbf1
-- tb1 :: (Symantics repr) => repr (o1 -> o11 -> o1)

-- Now that we've got a Symantics term, we can view it
tb1_view = view tb1
-- "(\\x0 -> (\\x1 -> x0))"


tb2 = reify ((base --> base) --> (base --> base)) bbf2
-- tb2 :: (Symantics repr) => repr ((o1 -> o1) -> o1 -> o1)

-- We can evaluate the reified term in many ways

tb2_eval = eval tb2 (succ) 0
-- 3

-- In the beta-eta normal form!

tb2_view = view tb2
-- "(\\x0 -> (\\x1 -> (x0 (x0 (x0 x1)))))"

-- * //
-- * Duality of reify/reflect
-- *  reflect . reify = eq_meta
-- *  reify . reflect = eq_obj
-- Where eq_meta is the equality of meta-terms and eq_obj is the equality
-- of object terms. What sort of equality? Often this question is
-- elided or hand-waved, which is a pity.

-- Let's take an example of the type a -> a, where reify_aa is lam and
-- reflect_aa is app.
-- app . lam 
-- == \f -> app (lam f)
-- == \f -> \e -> app (lam (\x -> f x)) e
-- {beta at obj level}
-- == \f -> \e -> f e == id_meta

-- lam . app
-- == \f -> lam (app f) 
-- == \f -> lam (\e -> app f e)
-- {eta at obj level}
-- == \f -> f == id_obj (since f has the type repr (a->a))
--
-- So, reflect/reify duality expresses beta-eta equivalence:
-- we should equate object terms modulo beta/eta.
-- This is the reason
-- * reify gives the object term representing the normal form of meta
-- * cf Normalization-by-evaluation
-- See the real form of bbf2. What we have printed is a
-- beta-eta-normal form.


main = do
       print tb1_view
       print tb2_eval
       print tb2_view
