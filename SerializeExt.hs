-- * Essentially, Haskell98
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Serialization and de-serialization in the tagless-final style
-- * for the extended data type
-- The deserialization problem is posed in
-- \url{http://userpages.uni-koblenz.de/~laemmel/TheEagle/}

-- * Solving the expression problem
-- What is the expression problem (see the slides)
-- We can: 
--   add new operations on the data type: we have just added
--   a serializer
--   Add a new expression form (multiplication)
-- We now see how we can extend the serializer and de-serializer.


module SerializeExt where

-- We really are re-using the existing code (which may already be compiled):
import Intro2 hiding (main)
import ExtF hiding (main)	     -- import the extended `variant': Mul

import Serialize (Tree(..),toTree)	     -- import the wire format
				     -- import the original serializer
import qualified Serialize as S	hiding (main)
import qualified Data.DList as D
import Data.DList (DList (..))
-- * //
-- First we extend the serializer

instance MulSYM Tree where
    mul e1 e2 = Node "Mul" [e1,e2]

-- And we serialize the extended terms

tfm1_tree = S.toTree tfm1
--  Node "Add" [Node "Lit" [Leaf "7"],
--    Node "Neg" [Node "Mul" [Node "Lit" [Leaf "1"],Node "Lit" [Leaf "2"]]]]

tfm2_tree = S.toTree tfm2
-- Node "Mul" [Node "Lit" [Leaf "7"],
--   Node "Add" [Node "Lit" [Leaf "8"],
--     Node "Neg" [Node "Add" [Node "Lit" [Leaf "1"],Node "Lit" [Leaf "2"]]]]]

-- * //
-- Let us now extend the de-serializer
-- We merely `add' one clause to the de-serializer of unextended terms.
-- We have not touched the code of the old de-serializer. The file
-- Serialize.hs could have been given to us in the compiled form.
-- We don't need the source code for it since we don't modify it and
-- don't recompile it.

-- The inferred signature is exactly as we wish:
-- fromTreeExt :: (MulSYM repr, ExpSYM repr) => (Tree -> repr) -> Tree -> repr

fromTreeExt self (Node "Mul" [e1,e2]) = mul (self e1) (self e2)
fromTreeExt self e = S.fromTreeExt self e -- use the old one for the rest

-- * Tie up the knot
fromTree = S.fix fromTreeExt		-- One does use fix in real programs

-- Now we can see the real benefit of using fix in real programs.
-- The fixpoint combinator is NOT a mere curiosity

-- We can de-serialize the unextended terms using the extended
-- de-serializer

tf1' = fromTree S.tf1_tree

tf1'_eval = eval tf1'
-- 5

tf1'_view = view tf1'
-- "(8 + (-(1 + 2)))"

-- We can now de-serialize the extended terms
tfm1' = fromTree tfm1_tree
tfm2' = fromTree tfm2_tree

-- And evaluate them in different interpreters

tfm1'_eval = eval tfm1'
-- 5

tfm1'_view = view tfm1'
-- "(7 + (-(1 * 2)))"


tfm2'_eval = eval tfm2'
-- 35

tfm2'_view = view tfm2'
-- "(7 * (8 + (-(1 + 2))))"

-- * Extending the deserializer has been an open problem!

-- Of course we had to write the deserializer in the open-recursion form.
-- We had to anticipate the extension.
-- But we had to extend the wire format, which is the 
-- input of the deserializer (rather than the expression, which
-- is the output of the deserializer). 
-- Whether we use the final tagless approach or not,
-- if we want deserializer to be extensible with respect to its
-- input (the wire format), we have to explicitly make it so.


main = do
       print tfm1_tree
       print tfm2_tree
       print tf1'_eval
       print tf1'_view
       print tfm1'_eval
       print tfm1'_view
       print tfm2'_eval
       print tfm2'_view

--  LocalWords:  serializer
