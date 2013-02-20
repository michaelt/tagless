{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-#LANGUAGE FlexibleInstances #-}
-- * Tagless Typed Interpreters: extensibility

module ExtF where

import Intro2 as F hiding (main)
import qualified Data.DList as D
import Data.DList (DList(..))
import Control.Monad (join)

-- We extend the final representation of the language with a new
-- expression form: multiplication

class MulSYM repr where
    mul :: repr -> repr -> repr

-- An extended sample expression
tfm1 = add (lit 7) (neg (mul (lit 1) (lit 2)))

-- We can even use a previously defined unextended expression (tf1)
-- as a part of the extended expression.
-- We can indeed mix-and-match
tfm2 = mul (lit 7) tf1

-- * //
-- We extend the specific interpreters thusly

instance MulSYM Int where
    mul e1 e2 = e1 * e2

instance MulSYM (DList a) where
  mul fs gs = Control.Monad.join $ D.map (\x ->  gs) fs
-- The definition of eval stays the same. Why?
-- * The extension _automatically_ kicks in
tfm1_eval = eval tfm1
-- 5
tfm2_eval = eval tfm2
-- 35

-- We `extend' the view interpreter just as well

instance MulSYM String where
    mul e1 e2 = "(" ++ e1 ++ " * " ++ e2 ++ ")"


tfm1_view = view tfm1
-- "(7 + (-(1 * 2)))"

tfm2_view = view tfm2
-- "(7 * (8 + (-(1 + 2))))"

-- * //
-- We can put the original, unextended expressions (F.tf1 from Intro2.hs)
-- and the extended ones (which we have just defined)
-- into the same list

tfl1 = [F.tf1]				-- old expression
tfl2 = tfm1 : tfm2 : tfl1		-- add extended expressions

-- The inferred type of tfl2 is insightful:
-- *ExtF> :t tfl1
-- tfl1 :: (ExpSYM repr) => [repr]
-- *ExtF> :t tfl2
-- tfl2 :: (ExpSYM repr, MulSYM repr) => [repr]

tfl2_eval = map eval tfl2
-- [5,35,5]

tfl2_view = map view tfl2
-- ["(7 + (-(1 * 2)))","(7 * (8 + (-(1 + 2))))","(8 + (-(1 + 2)))"]

main = do
       print tfm1_eval
       print tfm2_eval
       print tfm1_view
       print tfm2_view
       print tfl2_eval
       print tfl2_view
