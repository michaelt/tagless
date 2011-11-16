{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}


module CPS where

import qualified TTF as Sym

-- * Extending Symantics:
-- * Parameterizing the arrows by the interpreter

-- *  CBAny.hs: type Arr exp a b = exp a -> exp b
-- That is different from the R interpreter we did earlier.
-- Evaluating an object term rep (Arr a b) in CBAny
-- would give us a function, but not of the type a -> b.
-- In the case of R, it would be R a -> R b.
-- It didn't matter for CBAny: We can't observe functional 
-- values anyway. In contrast, the term (repr Int) was interpreted 
-- in CBAny as Haskell Int, which we can observe. 
-- Thus, CBAny is suitable for encoding ``the whole code'' (a typical program),
-- whose result is something we can observe (but not apply).

-- Can we be flexible and permit interpretations of
-- repr (a->b) as truly Haskell functions a->b?
-- We need to make the interpretations of arrows dependent
-- on a particular interpreter.

-- * Emulating ML modules in Haskell
-- Making arrows dependent on the interpreter looks better in OCaml: 
-- we write a signature that contains the type ('a,'b) arrow.
-- Different structures implementing the signature will specify
-- the concrete type for ('a,'b) arrow.
-- To emulate this facility -- structures (modules) containing not 
-- only values but also types -- we need type functions.
-- We can use multi-parameter type classes with functional dependencies.
-- It seems more elegant here to use type families.

-- * //
-- * How to interpret arrows and other types
type family Arr (repr :: * -> *) (a :: *) (b :: *) :: *

class ESymantics repr where
    int :: Int  -> repr Int
    add :: repr Int  -> repr Int -> repr Int

    lam :: (repr a -> repr b) -> repr (Arr repr a b)
    app :: repr (Arr repr a b) -> repr a -> repr b

-- * Like Symantics in CBAny.hs
-- The class declaration looks exactly like that in CBAny.hs.
-- However, there Arr was a type synonym. Here it is a type
-- function, indexed by repr.

-- * //
-- * All old Symantics terms can be re-interpreted in the
-- * extended Symantics
-- That is, we do not have to re-write the terms written
-- using the methods of the old Symantics (e.g., the terms
-- Sym.th1, Sym.th2, etc.) We merely have to re-interpret them,

-- generalizing the arrow
type family GenArr repr a :: *
type instance GenArr repr Int    = Int
type instance GenArr repr (a->b) = 
    Arr repr (GenArr repr a) (GenArr repr b)

newtype ExtSym repr a = ExtSym{unExtSym:: repr (GenArr repr a)}

-- The re-interpretation, essentially the identity
instance ESymantics repr => Sym.Symantics (ExtSym repr) where
    int       = ExtSym . int
    add e1 e2 = ExtSym $ add (unExtSym e1) (unExtSym e2)

    lam e     = ExtSym $ lam (unExtSym . e . ExtSym)
    app e1 e2 = ExtSym $ app (unExtSym e1) (unExtSym e2)


-- Sample terms

te1 = unExtSym Sym.th1 -- re-interpreting the old Symantics term th1
-- te1 = add (int 1) (int 2)
-- te1 :: (ESymantics repr) => repr Int

te2 = unExtSym Sym.th2
-- te2 = lam (\x -> add x x)
-- te2 :: (ESymantics repr) => repr (Arr repr Int Int)

-- We don't have to re-write th3 as te3; we merely re-interpret it
te3 = unExtSym Sym.th3
-- te3 = lam (\x -> (app x (int 1)) `add` (int 2))
-- te3 :: (ESymantics repr) => repr (Arr repr (Arr repr Int Int) Int)

te4 = let c3 = lam (\f -> lam (\x -> f `app` (f `app` (f `app` x))))
      in (c3 `app` (lam (\x -> x `add` int 14))) `app` (int 0)

-- The inferred type is interesting
-- te4
--   :: (Arr repr (Arr repr Int Int) (Arr repr Int Int)
--         ~
--       Arr repr (Arr repr Int Int) (Arr repr Int b),
--       ESymantics repr) =>
--      repr b
-- Because Arr is a type family, and type families are not
-- injective

-- * //
-- * The converse: ESymantics => Symantics
-- All extended symantics terms can be interpreted using
-- any old, legacy, Symantics interpeter
-- * Inject _all_ old interpreters into the new one
newtype Lg repr a = Lg{unLg :: repr a}

type instance Arr (Lg repr) a b = a -> b

instance Sym.Symantics repr => ESymantics (Lg repr) where
    int       = Lg . Sym.int
    add e1 e2 = Lg $ Sym.add (unLg e1) (unLg e2)
    lam e     = Lg $ Sym.lam (unLg . e . Lg)
    app e1 e2 = Lg $ Sym.app (unLg e1) (unLg e2)

legacy :: Sym.Symantics repr => (repr a -> b) -> Lg repr a -> b
legacy int e = int (unLg e)

-- * //
-- * We can use all existing interpreters _as they are_

te3_eval = legacy Sym.eval te3
-- te3_eval :: Arr (Lg Sym.R) (Arr (Lg Sym.R) Int Int) Int

te3_eval' = te3_eval id
-- 3

te3_view = legacy Sym.view te3
-- "(\\x0 -> ((x0 1)+2))"

te4_eval = legacy Sym.eval te4
-- 42

te4_view = legacy Sym.view te4
-- "(((\\x0 -> (\\x1 -> (x0 (x0 (x0 x1))))) (\\x0 -> (x0+14))) 0)"

-- We haven't gained anything though. Now we will

-- * //
-- * CBV CPS transform
-- *  CPS[ value ] = \k -> k $ CPSV[ value ]
-- *  CPS[ e1 e2 ] =
-- *   \k ->
-- *     CPS[ e1 ] (\v1 ->
-- *       CPS[ e2 ] (\v2 ->
-- *         v1 v2 k))
-- * (similar for addition)
-- *
-- *  CPSV[ basec ] = basec
-- *  CPSV[ x ]     = x
-- *  CPSV[ \x.e ]  = \x -> CPS[ e ]
-- We chose left-to-right evaluation order
-- * Danvy: CPS is *the* canonical transform
-- * CPS on types is NOT the identity
-- Why? Try to work out the types first

-- * //
newtype CPS repr w a = 
   CPS{cpsr :: repr (Arr repr (Arr repr a w) w)}
-- Here, w is the answer-type
-- We observe the similarity with the double negation
-- CPS is the transform: we use the arrows of the base interpreter

type instance Arr (CPS repr w) a b = 
   Arr repr a (Arr repr (Arr repr b w) w)

-- Auxiliary functions
-- Using (Arr repr a b) instead of (a->b) hinders the type
-- inference since type functions are not in general injective.
-- We need the following functions to constrain the types
-- so that the inference will work.
-- I wish there were a way to declare a type family injective!
cpsk :: ESymantics repr => (repr (Arr repr a w) -> repr w) -> CPS repr w a
cpsk = CPS . lam

appk :: ESymantics repr =>
	CPS repr w a -> (repr a -> repr w) -> repr w
appk (CPS e) f = app e $ lam f

-- * CPS of a value
cpsv :: ESymantics repr => repr a -> CPS repr w a
cpsv v = cpsk $ \k -> app k v

instance ESymantics repr => ESymantics (CPS repr w) where
    int x = cpsv $ int x
    add e1 e2 = cpsk $ \k ->
 		  appk e1 $ \v1 ->
 		  appk e2 $ \v2 ->
 		     app k (add v1 v2)
    lam e = cpsv $ lam (\x -> cpsr $ e (cpsv x))
    app ef ea = cpsk $ \k ->
 		  appk ef $ \vf ->
 		  appk ea $ \va ->
 		     app (app vf va) k


-- * //
-- * Applying the transform, evaluate afterwards

tec1 = cpsr te1
-- tec1 :: (ESymantics repr) => repr (Arr repr (Arr repr Int w) w)

-- We need to pass the identity continuation
tec1_eval = legacy Sym.eval tec1 id
-- 3

-- * The case of administrative redices
tec1_view = legacy Sym.view tec1
-- "(\\x0 -> ((\\x1 -> (x1 1)) 
--    (\\x1 -> ((\\x2 -> (x2 2)) (\\x2 -> (x0 (x1+x2)))))))"

-- The result is a bit of a mess: lots of administrative redices

tec2 = cpsr te2
tec2_eval = legacy Sym.eval tec2

-- The interpretation of a function is not usable, because of w...
-- Here we really need the answer-type polymorphism
-- OTH, like in CBAny.hs, the transform of a generally 'effectful'
-- function can be used in a `pure' code.
-- We can get a pure function out of tec2_eval; but
-- we have to do differently (from passing an identity continuation)
tec2_eval' = \a -> tec2_eval (\k -> k a id)
-- tec2_eval' :: Int -> Int

tec2_eval'' = tec2_eval' 21
-- 42

tec2_view = legacy Sym.view tec2
-- even bigger mess

tec4 = cpsr te4
tec4_eval = legacy Sym.eval tec4 id
-- 42

tec4_view = legacy Sym.view tec4
-- view is a mess... makes a good wall-paper pattern though...

-- * //
-- * Composing interpreters: doing CPS twice
-- We have already seen how to chain tagless final interpreters.
-- We push this further: we do CPS twice

tecc1 = cpsr tec1
-- The type makes it clear we did CPS twice

-- To evaluate the doubly-CPSed term, we have to do
-- more than just apply the identity continuation
-- flip($) is \v\k -> k v, which is sort of cpsv
tecc1_eval = legacy Sym.eval tecc1
tecc1_eval' = tecc1_eval (\k -> k (flip ($)) id)
-- 3

tecc1_view = legacy Sym.view tecc1
-- very big mess


-- * //
-- * One-pass CPS transform
-- Taking advantage of the metalanguage to get rid of the
-- administrative redices

newtype CPS1 repr w a = 
   CPS1{cps1r :: (repr a -> repr w) -> repr w}

reflect :: ESymantics repr =>
	   ((repr a -> repr w) -> repr w) ->
	   repr (Arr repr (Arr repr a w) w)
reflect e = lam (\k -> e (\v -> app k v))
-- * reflect e = lam (e . app)

-- The same as in CPS
-- After all, CPS1 is an optimization of CPS
type instance Arr (CPS1 repr w) a b = 
   Arr repr a (Arr repr (Arr repr b w) w)

-- * CPS1 of a value
cps1v :: ESymantics repr => repr a -> CPS1 repr w a
cps1v v = CPS1 $ \k -> k v

instance ESymantics repr => ESymantics (CPS1 repr w) where
    int x = cps1v $ int x
    add e1 e2 = CPS1 $ \k ->
 		  cps1r e1 $ \v1 ->
 		  cps1r e2 $ \v2 ->
 		     k (add v1 v2)

    lam e = cps1v $ lam $ reflect . cps1r . e . cps1v

    app ef ea = CPS1 $ \k ->
 		  cps1r ef $ \vf ->
 		  cps1r ea $ \va ->
 		     app (app vf va) (lam k)

cps1 = reflect . cps1r

-- * //
-- * Applying the transform, evaluate afterwards

tek1 = cps1 te1
-- tek1 :: (ESymantics repr) => repr (Arr repr (Arr repr Int w) w)

-- We need to pass the identity continuation
tek1_eval = legacy Sym.eval tek1 id
-- 3

-- * The result is indeed much nicer
-- Administrative redices are gone, serious operations
-- (like addition) remain
tek1_view = legacy Sym.view tek1
-- "(\\x0 -> (x0 (1+2)))"

tek2 = cps1 te2
tek2_eval = legacy Sym.eval tek2
tek2_eval'' = tek2_eval (\k -> k 21 id)
-- 42

-- Again, only serious redices remain
tek2_view = legacy Sym.view tek2
-- "(\\x0 -> (x0 (\\x1 -> (\\x2 -> (x2 (x1+x1))))))"


tek4 = cps1 te4
tek4_eval = legacy Sym.eval tek4 id
-- 42

tek4_view = legacy Sym.view tek4
-- The result is large, but comprehensible...
-- "(\\x0 -> 
--   (((\\x1 -> (\\x2 -> (x2 (\\x3 -> (\\x4 -> ((x1 x3) (\\x5 -> ((x1 x5) 
--                         (\\x6 -> ((x1 x6) (\\x7 -> (x4 x7)))))))))))) 
--     (\\x1 -> (\\x2 -> (x2 (x1+14))))) 
--   (\\x1 -> ((x1 0) (\\x2 -> (x0 x2))))))"

-- * //
-- * Composing interpreters: doing CPS twice
-- We have already seen how to chain tagless final interpreters.
-- We push this further: we do CPS twice

tekk1 = cps1 tek1
-- The type makes it clear we did CPS twice

tekk1_eval = legacy Sym.eval tekk1

-- tekk1_eval ::
--   (((Int -> (w1 ->w) -> w) -> (w1->w) -> w) -> w) -> w
tekk1_eval' = tekk1_eval (\k -> k (flip ($)) id)
-- 3

tekk1_view = legacy Sym.view tekk1
-- "(\\x0 -> (x0 (\\x1 -> (\\x2 -> ((x1 (1+2)) (\\x3 -> (x2 x3)))))))"
-- Can be eta-reduced
-- "(\\x0 -> (x0 (\\x1 -> (\\x2 -> ((x1 (1+2)) x2)))))"
-- "(\\x0 -> (x0 (\\x1 -> (x1 (1+2)) )))"

-- * Lessons
-- * The output of CPS is assuredly typed
-- * The conversion is patently total
-- * Composable transformers in the tagless final style



main = do
       print te3_eval'
       print te3_view
       print te4_eval
       print te4_view

       print tec1_eval
       print tec1_view
       print tec2_eval''
       print tec2_view
       print tec4_eval
       print tec4_view

       print tecc1_view
       print tecc1_eval'

       print tek1_eval
       print tek1_view
       print tek2_eval''
       print tek2_view
       print tek4_eval
       print tek4_view

       print tekk1_eval'
       print tekk1_view
