-- * Essentially, Haskell98
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Serialization and de-serialization in tagless-final style
-- The deserialization problem is posed in
-- \url{http://userpages.uni-koblenz.de/~laemmel/TheEagle/}

module Serialize where

import Intro2 hiding (main)


-- Data type of trees representing our expressions `on the wire'
-- All content is in the form of character string
-- Imagine the following to be XML, only more compact
data Tree = Leaf String			-- CDATA
	  | Node String [Tree]		-- element with its children
	    deriving (Eq, Read, Show)

-- Serializer for Exp -- just another interpreter, similar
-- to the ones we have seen

instance ExpSYM Tree where
    lit n = Node "Lit" [Leaf $ show n]
    neg e = Node "Neg" [e]
    add e1 e2 = Node "Add" [e1,e2]

toTree :: Tree -> Tree
toTree = id

-- tf1 = add (lit 8) (neg (add (lit 1) (lit 2)))
-- Our sample term
tf1_tree = toTree tf1

-- Looks like XML..
-- Node "Add" [Node "Lit" [Leaf "8"],
--    Node "Neg" [Node "Add" [Node "Lit" [Leaf "1"],Node "Lit" [Leaf "2"]]]]

-- * //
-- The problem is to write a 
-- * deserializer: take a tree and produce a term
-- * Challenge: maintain multiple interpretations
-- The result can be interpreted in any existing or future interpreter
-- That is a challenging part

-- The deserializer is necessarily a partial function: the input
-- may be ill-formed. For example: 
-- * possible bad input: Node "Lit" [Leaf "1", Leaf "2"]
-- A literal expression may have only one argument.

-- The result of the deserializer is something that can be interpreted
-- by any tagless interpreter. In short, the result should have the type
-- like our sample term 
-- * tf1 :: (ExpSYM repr) => repr
-- Alas, that term is polymorphic over repr. 
-- We can imagine deserializer as a recursive function that builds
-- a `term' bottom up. So, it needs to pass around such terms.
-- But polymorphic terms are not first-class in Hindley-Milner type system!
-- We can't pass around polymorphic terms -- only monomorphic instances
-- of them. Problem?
-- Well, in Haskell we actually do have 
-- * First-class polymorphism:
-- * newtype Wrapped = Wrapped{unWrap :: forall repr. ExpSYM repr => repr}
-- Our deserializer will produce a Wrapped value, which we will
-- have to unwrap to get to the desired term.

-- Let's try however the naive thing...

-- * //

-- fromTree :: ExpSYM repr => Tree -> repr
fromTree (Node "Lit" [Leaf n]) = lit $ read n
fromTree (Node "Neg" [e]) = neg (fromTree e)
fromTree (Node "Add" [e1,e2]) = add (fromTree e1) (fromTree e2)
fromTree e = error $ "Invalid tree: " ++ show e

-- What happened? Why it worked?
-- The clearest example of the power of ignorance. Sometimes knowing little
-- (about polymorphic recursion, first-class polymorphism, etc) hurts.
-- Was it polymorphic recursion? (Hint: no signature was required)

-- We can deserialize our sample term
tf1' = fromTree tf1_tree

-- And sure we can evaluate it with any of the existing interpreters

tf1'_eval = eval tf1'
-- 5

tf1'_view = view tf1'
-- "(8 + (-(1 + 2)))"

-- * Does each evaluation of tf1' re-parses tf1_tree?
-- We examine this issue in TypeCheck.hs


-- * //
-- Let us write the deserializer in the style of open recursion
-- we shall see the benefit later

-- The signature could have been inferred
fromTreeExt :: (ExpSYM b) => (Tree -> b) -> Tree -> b
fromTreeExt self (Node "Lit" [Leaf n]) = lit $ read n
fromTreeExt self (Node "Neg" [e]) = neg (self e)
fromTreeExt self (Node "Add" [e1,e2]) = add (self e1) (self e2)
fromTreeExt self e = error $ "Invalid tree: " ++ show e

-- we use the fixpoint combinator to tie up the knot

fix f = f (fix f)

fromTree' = fix fromTreeExt		-- One does use fix in real programs

tf1'' = fromTree' tf1_tree

tf1''_eval = eval tf1''
-- 5

tf1''_view = view tf1''
-- "(8 + (-(1 + 2)))"



main = do
       print tf1_tree
       print tf1'_eval
       print tf1'_view
       print tf1''_eval
       print tf1''_view


--  LocalWords:  deserialization Serializer deserializer
