{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types, ExistentialQuantification #-}

-- * Type representation, equality and the safe typecast:
-- * the above-the-board version of Data.Typeable

module Typ where

import Control.Monad
import Control.Monad.Error


-- * The language of type representations: first-order and typed
-- It is quite like the language of int/neg/add we have seen before,
-- but it is now typed.
-- It is first order: the language of simple types is first order

class TSYM trepr where
    tint :: trepr Int
    tarr :: trepr a -> trepr b -> trepr (a->b)

-- * The view interpreter
-- The first interpreter is to view the types

newtype ShowT a = ShowT String

instance TSYM ShowT where
    tint = ShowT $ "Int"
    tarr (ShowT a) (ShowT b) = ShowT $ "(" ++ a ++ " -> " ++ b ++ ")"

view_t :: ShowT a -> String
view_t (ShowT s) = s

-- * //
-- * Quantifying over the TSYM interpreter
-- This closes the type universe

newtype TQ t = TQ{unTQ :: forall trepr. TSYM trepr => trepr t}

-- TQ is itself an interpreter, the trivial one
instance TSYM TQ where
    tint = TQ tint
    tarr (TQ a) (TQ b) = TQ (tarr a b)

-- Sample type expressions

tt1 = (tint `tarr` tint) `tarr` tint
-- tt1 :: (TSYM trepr) => trepr ((Int -> Int) -> Int)

tt2 = tint `tarr` (tint `tarr` tint)
-- tt2 :: (TSYM trepr) => trepr (Int -> Int -> Int)

tt1_view = view_t (unTQ tt1)
-- "((Int -> Int) -> Int)"

tt2_view = view_t (unTQ tt2)
-- "(Int -> (Int -> Int))"

-- * //
-- * Show Typ-able expressions
-- * No Show type class constraint!

-- The signature is quite like gshow in a generic programming
-- library such as EMGM or LIGD
show_as :: TQ a -> a -> String
show_as tr a = 
    case unTQ tr of ShowAs _ f -> f a

-- The implementation of the interpreter ShowAs shows off
-- the technique of accumulating new TQ as we traverse the old
-- one. We shall see more examples later.
-- One is again reminded of attribute grammars.

data ShowAs a = ShowAs (TQ a) (a -> String)

instance TSYM ShowAs where
    tint = ShowAs tint show  -- as Int
    tarr (ShowAs t1 _) (ShowAs t2 _) =
        let t = tarr t1 t2 in
	ShowAs t (\_ ->  "<function of the type " ++ 
	                 view_t (unTQ t) ++ ">")
tt0_show = show_as tint 5
-- "5"

tt1_show = show_as tt1 undefined
-- "<function of the type ((Int -> Int) -> Int)>"

-- We can't show functional values, but at least we should be
-- able to show their types

-- * //
-- * Type representation
-- * Compare with Dyta.Typeable.TypeRep
-- It is not a data structure!
data Typ = forall t. Typ (TQ t)


-- * //
-- * Alternative to quantification: copying
-- Before instantiating one interpreter, we fork it.
-- One copy can be instantiated, but the other remains polymorphic
-- Compare with Prolog's copy_term
-- This approach keeps the type universe extensible
-- Again the same pattern: traverse one TQ and build another
-- (another two actually)

data TCOPY trep1 trep2 a = TCOPY (trep1 a) (trep2 a)

instance (TSYM trep1, TSYM trep2) 
    => TSYM (TCOPY trep1 trep2)
  where
    tint = TCOPY tint tint
    tarr (TCOPY a1 a2) (TCOPY b1 b2) = 
	TCOPY (tarr a1 b1) (tarr a2 b2)

-- * //
-- * Equality and safe type cast

-- * c is NOT necessarily a functor or injective!
-- For example, repr is not always a functor
-- I wonder if we can generalize to an arbitrary type function
-- represented by its label lab:
-- newtype EQU a b = EQU (forall lab. (Apply lab a -> Apply lab b)
-- That would let us _easily_ show, for example, that
-- EQU (a,b) (c,d) implies EQU a c, for all types a, b, c, d.

newtype EQU a b = EQU{equ_cast:: forall c. c a -> c b}

-- * Leibniz equality is reflexive, symmetric and transitive
-- Here is the constructive proof

refl :: EQU a a
refl = EQU id

-- * An Unusual `functor'
tran :: EQU a u -> EQU u b -> EQU a b
tran au ub = equ_cast ub au
-- Why it works? We consider (EQU a u) as (EQU a) u,
-- and so instantiate c to be EQU a

newtype FS b a = FS{unFS:: EQU a b}

symm :: EQU a b -> EQU b a
symm equ = unFS . equ_cast equ . FS $ refl

-- Useful type-level lambdas, so to speak
newtype F1 t b a = F1{unF1:: EQU t (a->b)}

newtype F2 t a b = F2{unF2:: EQU t (a->b)}

eq_arr :: EQU a1 a2 -> EQU b1 b2 -> EQU (a1->b1) (a2->b2)
eq_arr a1a2 b1b2 = 
    unF2 . equ_cast b1b2 . F2 . unF1 . equ_cast a1a2 . F1 $ refl

-- How does this work? what is the type of refl above?

-- * //
-- * Decide if (trepr a) represents a type that is equal to some type b
-- Informally, we compare a value that _represents_ a type b
-- against the _type_ b

-- We do that by interpreting trepr a in a particular way

-- * A constructive `deconstructor'
data AsInt a = AsInt (Maybe (EQU a Int))

instance TSYM AsInt where
    tint     = AsInt $ Just refl
    tarr _ _ = AsInt $ Nothing

-- This function proves useful later
as_int :: AsInt a -> c a -> Maybe (c Int)
as_int (AsInt (Just equ)) r = Just $ equ_cast equ r
as_int _ _ = Nothing

-- * Another constructive `deconstructor'

data AsArrow a = 
    forall b1 b2. AsArrow (TQ a) (Maybe (TQ b1, TQ b2, EQU a (b1->b2)))

instance TSYM AsArrow where
    tint       = AsArrow tint Nothing
    tarr (AsArrow t1 _) (AsArrow t2 _) = 
	         AsArrow (tarr t1 t2) $ Just (t1,t2,refl)

as_arrow :: AsArrow a -> AsArrow a
as_arrow = id

-- More cases could be added later on...

newtype SafeCast a = SafeCast (forall b. TQ b -> Maybe (EQU a b))

instance TSYM SafeCast where
    tint = SafeCast $ \tb -> 
	     case unTQ tb of AsInt eq -> fmap symm eq
    tarr (SafeCast t1) (SafeCast t2) = 
	 SafeCast $ \tb -> do
	     AsArrow _ (Just (b1,b2,equ_bb1b2)) <- 
		 return $ as_arrow (unTQ tb)
	     equ_t1b1 <- t1 b1
	     equ_t2b2 <- t2 b2
	     return $ tran (eq_arr equ_t1b1 equ_t2b2) (symm equ_bb1b2)


-- * Cf. Data.Typeable.gcast
-- Data.Typeable.gcast :: (Data.Typeable.Typeable b, Data.Typeable.Typeable a) =>
--                         c a -> Maybe (c b)
-- We use our own `Typeable', implemented without
-- invoking GHC internals

safe_gcast :: TQ a -> c a -> TQ b -> Maybe (c b)
safe_gcast (TQ ta) ca tb = cast ta
 where cast (SafeCast f) = 
	 maybe Nothing (\equ -> Just (equ_cast equ ca)) $ f tb

-- There is a tantalizing opportunity of making SafeCast extensible

-- * //
-- * Our own version of Data.Dynamic
-- We replace Data.Typeable with TQ a

data Dynamic = forall t. Dynamic (TQ t) t

tdn1 = Dynamic tint 5

tdn2 = Dynamic tt1 ($ 1)

tdn3 = Dynamic (tint `tarr` (tint `tarr` tint)) (*)

tdn_show (Dynamic tr a) = show_as tr a

newtype Id a = Id a
tdn_eval1 (Dynamic tr d) x = do
  Id f <- safe_gcast tr (Id d) tt1
  return . show $ f x

tdn_eval2 (Dynamic tr d) x y = do
  Id f <- safe_gcast tr (Id d) tt2 
  return . show $ f x y

tdn1_show = tdn_show tdn1
-- "5"

tdn2_show = tdn_show tdn2
-- "<function of the type ((Int -> Int) -> Int)>"

tdn3_show = tdn_show tdn3
-- "<function of the type (Int -> (Int -> Int))>"

tdn1_eval = tdn_eval1 tdn1 (+4)
-- Nothing

tdn2_eval = tdn_eval1 tdn2 (+4)
-- Just "5"

tdn2_eval' = tdn_eval2 tdn2 3 14
-- Nothing

tdn3_eval = tdn_eval2 tdn3 3 14
-- Just "42"


main = do
       print tt1_view
       print tt2_view
       print tt0_show
       print tt1_show
       print tdn1_show
       print tdn2_show
       print tdn3_show
       print tdn1_eval
       print tdn2_eval
       print tdn2_eval'
       print tdn3_eval
