{-# LANGUAGE GADTs #-}

-- * Tagless initial and final evaluators for simply-typed lambda-calculus
-- based on the code accompanying the paper by
--   Jacques Carette, Oleg Kiselyov, and Chung-chieh Shan
-- The language is simply typed lambda-calculus with booleans,
-- and de Bruijn encoding of variables.

module IntroHOIF where

-- * The initial encoding

-- From our experience with the tagfull evaluator, we learned
-- that we need to parameterize the expression type by the
-- type of the result and by the environment, so to distinguish
-- the open terms.
-- We need GADTs. In fact, the present example was the motivation
-- for GADTs.

data Var env t where
    VZ :: Var (t,env) t			-- Assumption axiom
    VS :: Var env t -> Var (a,env) t    -- Weakening

data Exp env t where
    B :: Bool -> Exp env Bool		-- Axiom: Boolean literal has type Bool
					-- in any environment
    V :: Var env t -> Exp env t		-- Reference to a hypothesis
    L :: Exp (a,env) b -> Exp env (a->b)          -- Implication introduction
    A :: Exp env (a->b) -> Exp env a -> Exp env b -- Implication elimination

-- * Exp represents only well-typed object terms
-- * Axioms of minimal logic
-- We can read the axioms and inference rules of minimal logic just
-- from the above definition

-- This is like lookp in IntroHOT.hs, only the environment is a
-- heterogeneous list (a nested tuple) rather than an ordinary list
lookp :: Var env t -> env -> t
lookp VZ (x,_) = x
lookp (VS v) (_,env) = lookp v env

-- This is exactly the evaluator we wanted to write in IntroHOT.hs
-- With GADTs, we can.
-- No longer universal type, no longer type tagging, no longer
-- partial pattern matching (in A and in lookp)
eval :: env -> Exp env t -> t
eval env (V v) = lookp v env
eval env (B b) = b
eval env (L e) = \x -> eval (x,env) e
eval env (A e1 e2) = (eval env e1) (eval env e2)

-- * Pattern-match should always succeed now
-- * (but does GHC notice this)?

-- A sample term
ti1 = A (L (V VZ)) (B True)
ti1_eval = eval () ti1
-- Now we get the true boolean
-- *IntroHOIF> :t ti1_eval
-- ti1_eval :: Bool
-- *IntroHOIF> ti1_eval
-- True

-- A more elaborate sample term
ti2 = (A (A (L (L (V (VS VZ)))) (B True)) (B False))
ti2_eval = eval () ti2
-- True

-- Problematic terms:

-- Can't even write this any more
-- * ti2a = A (B True) (B False)
--     Couldn't match expected type `a -> b' against inferred type `Bool'
--       Expected type: Exp env (a -> b)
--       Inferred type: Exp env Bool
--     In the first argument of `A', namely `(B True)'
--     In the expression: A (B True) (B False)

ti2o = A (L (V (VS VZ))) (B True)

-- IntroHOIF> eval () ti2o
-- <interactive>:1:8:
--     Couldn't match expected type `Exp () t'
--            against inferred type `(t1, t11) -> t1'
--     In the second argument of `eval', namely `ti3'
--     In the expression: eval () ti3
--
-- The reason is clear from the inferred type of ti3
-- IntroHOIF> :t ti3
-- ti3 :: (t, t1) -> t
-- The term requires a non-empty environment: it's an open term!

-- * //
-- * Do we need fancy types? Can HM suffice?
-- But do we really need dependent types (or even GADTs)?
-- Now we introduce the final approach: it is Haskell98 (in fact, just HM)

-- vz :: (t, t1) -> t
vz (vc,_) = vc
vs vp (_,envr) = vp envr

b bv env = bv
l e env = \x -> e (x,env)
a e1 e2 env = (e1 env) (e2 env)

-- A sample term
tf1 = a (l vz) (b True)
tf1_eval = tf1 ()

-- The inferred type is:
-- tf1_eval :: Bool
-- True
-- No tagging any more

tf2 = (a (a (l (l (vs vz))) (b True)) (b False))
tf2_eval = tf2 ()
-- True

-- * Only well-typed terms are expressible, 
-- * only closed terms can be evaluated
-- * There are no variant types, cannot be pattern-match failures

-- * tf2a = a (b True) (b False)
-- Cannot write this term, just as we couldn't write ti2a

tf2o = a (l (vs vz)) (b True)

-- The inferred type shows that tf2o takes a non-empty environment
-- It is an open term!
-- tf2o :: (t, t1) -> t

-- Can't evaluate the open term
-- tf2o_eval = tf2o ()
--  Couldn't match expected type `(t, t1)' against inferred type `()'


tf5_eval = (a 
	    (a (l (l (a (a (vs vz) (b True)) vz)))
               (l (l vz)))
	    (b False)) ()
-- False

-- * Why this is NOT a Church-encoding 
-- a,l,b are not a Church encoding of Exp of IntroHOT.hs
-- because Exp is `too big' (contains ill-typed terms).
-- But a,l,b represent only well-typed terms.
-- Also, the result is not a Church encoding of the Universal
-- type. See this clause
--    a e1 e2 env = (e1 env) (e2 env)
-- (e1 env) has a single continuation
-- If the value of (e1 env) were the Church encoding of 
-- the Universal type in IntroHOT.hs we should have provided two
-- continuations (for the B variant).

-- Ill-typed terms cannot even be written!
-- t61 = (l (a vz vz))
--     Occurs check: cannot construct the infinite type: t = t -> t1

{-
t62 = a (l (a vz (b True))) (b False)

    Couldn't match expected type `Bool -> t'
           against inferred type `Bool'
    In the second argument of `a', namely `(b False)'
    In the expression: a (l (a vz (b True))) (b False)
-}


main = do
       print ti1_eval
       print ti2_eval
       print tf1_eval
       print tf2_eval
       print tf5_eval


