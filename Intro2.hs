{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- * Tagless Typed Interpreters, introduction

module Intro2 where
import qualified Data.DList as D
import Data.DList (DList(..))
-- Parameterizing the final interpreter over the type Repr

class ExpSYM repr where
    lit :: Int -> repr
    neg :: repr -> repr
    add :: repr -> repr -> repr

-- Compared to the signatures of lit, neg and add in Intro1.hs,
-- repr is now in lower-case

-- * cf. Denotational Semantics
-- The declaration of ExpSYM should remind one even more of
-- denotational semantics: think of 'repr' as the semantic domain
-- The declaration of ExpSYM patently expresses that semantics is
-- _compositional_
instance ExpSYM (DList a) where
  lit n = DL $ \xs -> (Prelude.foldr (.) id $ replicate n (xs ++)) xs 
  neg (DL fxs) =  DL (reverse . fxs)
  add  (DL fxs) (DL gxs) = DL (fxs . gxs)

interpret :: DList a -> DList a
interpret = id

tfdl1 = add (lit 1) (neg (lit 2))

(<>) :: [a] -> DList a -> [a]
xs <> (DL fs) = fs xs

-- Our sample expression in the final form
tf1 = add (lit 8) (neg (add (lit 1) (lit 2)))

-- * We represent object terms not by its abstract syntax (initial)
-- * but by its denotation in a semantic algebra.
-- That's why we call the approach `final'

-- What is its inferred type?
-- Why should we disable the monomorphism restriction?

-- * //
instance ExpSYM Int where
    lit n = n
    neg e = - e
    add e1 e2 = e1 + e2

-- A strange type and form for the eval, isn't it?
-- Why is that?
eval :: Int -> Int
eval = id

-- Of course, the more precise name for eval would be
-- ``an interpretation that returns an integer''
-- There may be many interpretations that return an Int.
-- We should use `newtype' wrappers to distinguish them.

-- A participant has remarked that ExpSym looks like
-- a threaded Forth interpreter. The analogy is apt:
-- there is no instruction dispatch (on data constructors
-- in Intro1.hs).

tf1_eval = eval tf1 
-- 5


-- * SYM stands for Symantics: the class defines the syntax,
-- * and instances define the semantics

-- Now we can write a different evaluator

instance ExpSYM String where
    lit n = show n
    neg e = "(-" ++ e ++ ")"
    add e1 e2 = "(" ++ e1 ++ " + " ++ e2 ++ ")"

view :: String -> String
view = id

tf1_view = view tf1 
-- "(8 + (-(1 + 2)))"

-- One may love this approach: view and eval don't do
-- anything (they are the identity), but give the right
-- result anyway.

main = do
       print tf1_eval
       print tf1_view

--  LocalWords:  ExpSYM Repr repr monomorphism eval SYM Symantics
