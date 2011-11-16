{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types, ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies, UndecidableInstances #-}

-- * Why all these extensions
-- I could've cheated a bit and gotten by without the last four:
-- the function typecheck below is partial anyway.
-- If we permit one sort of errors (when the deserialized term is
-- ill-typed), we may as well permit another sort of errors
-- (a closed-looking term turns out open), even if the
-- latter sort of  error can't arise if our typecheck function is correct.
-- *  -- due to the desire to let GHC check some correctness properties
-- I wanted to avoid unnecessary errors and let GHC see the
-- correctness of my code to a larger extent

module TypeCheck where

-- * No Data.Typeable, no gcast. Everything is above the board
-- * No import Data.Typeable
import Typ hiding (main)                -- Our version of Typeable
import Control.Monad
import Control.Monad.Error

import TTFdB hiding (main)		-- we use de Bruijn indices



-- * Data type of trees representing our expressions `on the wire'
-- * Serialized expressions are _untyped_
-- All content is in the form of character string
-- Imagine the following to be XML, only more compact
data Tree = Leaf String			-- CDATA
	  | Node String [Tree]		-- element with its children
	    deriving (Eq, Read, Show)


-- * Expression format (extensible)
-- *  Node "Int" [Leaf number]    -- int literal
-- *  Node "Add" [e1,e2]          -- addition
-- *  Node "App" [e1,e2]          -- application
-- *  Node "Var" [Leaf name]
-- *  Node "Lam" [Leaf name,e1,e2] -- e2 is body, e1 is type of var
-- *  ...
-- *
-- * Format of types
-- *  Node "TInt" []		-- Int
-- *  Node "TArr" [e1,e2]       -- e1 -> e2
-- *  ...

-- * Serialized expressions are in the Church-style
-- so that we won't need inference, only type checking
-- Inference is not hard here; It is orthogonal and obscures our goal
-- here of deserialization into a typed term

-- * //
-- * Desiderata
-- * Type check once, interpret many times
-- *   detect type-checking error _before_ evaluation
-- so that the evaluators can't possibly fail because
-- the serialized expression was ill-typed. That error should be
-- detected and handled earlier.
-- Desired function:
-- typecheck :: Tree -> ???
-- We will use de-Bruijn indices (why?)
-- typecheck :: Symantics repr => Tree -> repr h ???
-- We can use something like read:
--   read :: Read a => String -> a
-- but that defeats the purpose since we must know a.
-- We may want to deserialize the term and print it out. If our
-- typecheck is like read, we get the read-show problem.
-- * Avoiding read-show problem
-- We have to abstract over a: need Dynamics, or existentials

-- * Typing dynamic typing
-- * Type-safe cast

-- * //
-- Old approach (see IncopeTypecheck.hs)
-- The Show constraint is for debugging, so to see the result
-- DynTerm repr h should be the result of typecheck
-- * data DynTerm repr h = forall a. (Show a, Typeable a) => DynTerm (repr h a)

data DynTerm repr h = forall a. DynTerm (TQ a) (repr h a)

-- A sample `dynamic' object term
tdyn1 = DynTerm tint (lam z `app` (int 1))

-- Interpret many times
tdyn1_eval = case tdyn1 of DynTerm tr t -> show_as tr $ eval t
-- "1"

-- This test particularly shows that we don't even need to know
-- the type of term; eventually we get the string
tdyn1_view = case tdyn1 of DynTerm _ t -> view t
-- "((\\x0 -> x0) 1)"


-- * //
-- * De-serialize type expressions
-- The serialized terms contain type annotations on bound variables.
-- We need to read the annotations and convert them to Haskell types.
-- But Haskell types are not terms! So, we have to produce a term
-- with the desired Haskell type: Typ.Typ

-- * Error monad, to report deserialization errors

-- The function read_t below is necessarily partial:
-- the type annotation in the Tree form can be wrong, for example,
-- (Node "Tarr" []).
-- To report the error meaningfully, we use the Error monad

-- We should have written read_t in the open recursion style,
-- so that it would be extensible.
-- But we omit the type extensibility here for the sake of clarity

read_t :: Tree -> Either String Typ
read_t (Node "TInt" [])  = return $ Typ tint
read_t (Node "TArr" [e1,e2]) = do
  Typ t1 <- read_t e1
  Typ t2 <- read_t e2
  return . Typ $ tarr t1 t2
read_t tree = fail $ "Bad type expression: " ++ show tree

-- * A few explanations are in order
-- The TArr clause operates on `some' types t1 and t2


-- * //
-- * Type checking environment
-- Our deserializer `typecheck' is too necessarily partial.
-- Again we will use the error monad to report errors.
-- Thus the tentative type for typecheck is
-- * typecheck :: Symantics repr => 
-- *	     Tree -> Either String (DynTerm h repr)
--
-- * Open terms may legitimately occur
-- First of all, when processing the body of abstractions.
-- Second, we may use `global constants' (standard Prelude, of sorts).
-- We therefore type-check in the type environment Gamma,
-- which is a map from variable names to their types. Hence
-- type-check should have this signature:
-- * typecheck :: Symantics repr => 
-- *	     Tree -> Gamma -> Either String (DynTerm h repr)
-- But Gamma and h are related! We should make it explicit that
-- Gamma (type checking environment) determines h (the run-time environment
-- of a term).
-- *   Gamma is a compile-time environment: contains variable names
-- *   h is a run-time environment: contains values
-- Both environments are indexed by types of their elements; 
-- since h is a nested tuple, so should be Gamma

type VarName = String
data VarDesc t = -- Component of Gamma
    VarDesc (TQ t) VarName 

-- * Relating Gamma and h
class Var gamma h | gamma -> h where
    findvar :: Symantics repr =>
	       VarName -> gamma -> Either String (DynTerm repr h)

-- Like asTypeOf, used to specialize polymorphic term repr h t
-- to a specific type t
asTypeRepr :: t -> repr h t -> repr h t
asTypeRepr _ = id

instance Var () () where
    findvar name _ = fail $ "Unbound variable: " ++ name

instance Var gamma h => Var (VarDesc t,gamma) (t,h) where
    findvar name (VarDesc tr name',_) | name == name' =
	 return $ DynTerm tr z

    findvar name (_,gamma) = do
         DynTerm tr v <- findvar name gamma
	 return $ DynTerm tr (s v)


-- * //
typecheck :: (Symantics repr, Var gamma h) =>
	     Tree -> gamma -> Either String (DynTerm repr h)

typecheck (Node "Int" [Leaf str]) gamma =
    case reads str of
      [(n,[])] -> return $ DynTerm tint (int n)
      _        -> fail $ "Bad Int literal: " ++ str

typecheck (Node "Add" [e1, e2]) gamma = do
  DynTerm (TQ t1) d1 <- typecheck e1 gamma
  DynTerm (TQ t2) d2 <- typecheck e2 gamma
  case (as_int t1 d1, as_int t2 d2) of
    (Just t1', Just t2') -> return . DynTerm tint $ add t1' t2'
    (Nothing,_) -> fail $ "Bad type of a summand: " ++ view_t t1
    (_,Nothing) -> fail $ "Bad type of a summand: " ++ view_t t2


typecheck (Node "Var" [Leaf name]) gamma = findvar name gamma

typecheck (Node "Lam" [Leaf name,etyp,ebody]) gamma = do
  Typ ta <- read_t etyp
  DynTerm tbody body  <- typecheck ebody (VarDesc ta name, gamma)
  return $ DynTerm (tarr ta tbody) (lam body)

typecheck (Node "App" [e1, e2]) gamma = do
  DynTerm (TQ t1) d1 <- typecheck e1 gamma
  DynTerm (TQ t2) d2 <- typecheck e2 gamma
  AsArrow _ arr_cast <- return $ as_arrow t1
  let errarr = fail $ "operator type is not an arrow: " ++ view_t t1
  (ta,tb,equ_t1ab) <- maybe errarr return arr_cast
  let df = equ_cast equ_t1ab d1
  case safe_gcast (TQ t2) d2 ta of 
    Just da -> return . DynTerm tb $ app df da
    _ -> fail $ unwords ["Bad types of the application:", 
 			 view_t t1, "and", view_t t2]

typecheck e gamma = fail $ "Invalid Tree: " ++ show e

-- Why the app case is complex, more complex than Add
-- The type of the argument is, well, existential

-- * //
-- * Simple tests

tx1 = typecheck 
       (Node "Var" [Leaf "x"]) ()

tx2 = typecheck 
       (Node "Lam" [Leaf "x",Node "TInt" [],
		    Node "Var" [Leaf "x"]]) ()
tx3 = typecheck 
       (Node "Lam" [Leaf "x",Node "TInt" [],
	  Node "Lam" [Leaf "y",Node "TInt" [],
		    Node "Var" [Leaf "x"]]]) ()

tx4 = typecheck 
       (Node "Lam" [Leaf "x",Node "TInt" [],
	  Node "Lam" [Leaf "y",Node "TInt" [],
	    Node "Add" [Node "Int" [Leaf "10"],
			Node "Var" [Leaf "x"]]]]) ()


tx_view t = case t of
		 Right (DynTerm _ t) -> view t
		 Left err -> error err

tx1_view = tx_view tx1

tx4_view = tx_view tx4
-- "(\\x0 -> (\\x1 -> (10+x0)))"

-- * //
-- * Closed interpreter
-- to convert a monomorphic binding to polymorphic in tc_evalview
-- below.

newtype CL h a = CL{unCL :: forall repr. Symantics repr => repr h a}

instance Symantics CL where
    int x     = CL $ int x
    add e1 e2 = CL $ add (unCL e1) (unCL e2)
    z         = CL z
    s v       = CL $ s (unCL v)
    lam e     = CL $ lam (unCL e)
    app e1 e2 = CL $ app (unCL e1) (unCL e2)

-- * //
-- * Main tests
-- * Type-check once, evaluate many times
-- One may worry that each time we evaluate a deserialized term,
-- we are type checking it from scratch.
-- The following shows that it is not the case:
-- if Tree represents an ill-typed term, we determine an error
-- before we started evaluating it (many times).

tc_evalview exp = do
 DynTerm tr d <- typecheck exp ()
 let d' = unCL d				-- Make d polymorphic again
 return $ (show_as tr $ eval d',
	   view d')
 
-- * A few combinators to help build trees
-- XML, or even its abstractions, are too verbose
tr_int x = Node "Int" [Leaf $ show x]
tr_add e1 e2 = Node "Add" [e1, e2]
tr_app e1 e2 = Node "App" [e1, e2]
tr_lam v t e = Node "Lam" [Leaf v, t, e]
tr_var v = Node "Var" [Leaf v]

tr_tint = Node "TInt" []
tr_tarr t1 t2 = Node "TArr" [t1,t2]


-- dt1:: Symantics repr => DynTerm repr ()
dt1 = tc_evalview (tr_add (tr_int 1) (tr_int 2))
-- Right ("3","(1+2)")

dt2 = tc_evalview (tr_app (tr_int 1) (tr_int 2))
-- Left "operator type is not an arrow: Int"

dt4 = tc_evalview 
       (tr_lam "x" tr_tint (tr_lam "y" (tr_tint `tr_tarr` tr_tint) 
	    (tr_lam "z" tr_tint (tr_var "y"))))
-- Right ("<function of the type (Int -> ((Int -> Int) -> (Int -> (Int -> Int))))>",
--        "(\\x0 -> (\\x1 -> (\\x2 -> x1)))")

dt41 = tc_evalview 
         (tr_lam "x" tr_tint (tr_lam "y" (tr_tint `tr_tarr` tr_tint) 
	    (tr_lam "z" tr_tint (tr_var "x"))))
-- Right ("<function of the type (Int -> ((Int -> Int) -> (Int -> Int)))>",
--        "(\\x0 -> (\\x1 -> (\\x2 -> x0)))")


dt5 = tc_evalview (tr_lam "x" tr_tint (tr_add (tr_var "x") (tr_int 1)))
-- Right ("<function of the type (Int -> Int)>",
--        "(\\x0 -> (x0+1))")

-- Making a deliberate mistake...
dt6 = tc_evalview (tr_lam "x" (tr_tint `tr_tarr` tr_tint)
	            (tr_add (tr_var "x") (tr_int 1)))
-- Left "Bad type of a summand: (Int -> Int)"

-- Untyped Church Numeral 2
exp_n2 = (tr_lam "f" (tr_tint `tr_tarr` tr_tint)
          (tr_lam "x" tr_tint
	      (tr_app (tr_var "f") (tr_app (tr_var "f") (tr_var "x")))))

dt7 = tc_evalview exp_n2
-- Right ("<function of the type ((Int -> Int) -> (Int -> Int))>",
--        "(\\x0 -> (\\x1 -> (x0 (x0 x1))))")

dt8 = tc_evalview 
        (tr_app (tr_app exp_n2 
           (tr_lam "x" tr_tint (tr_add (tr_var "x") (tr_var "x"))))
           (tr_int 11))
-- Right ("44",
--        "(((\\x0 -> (\\x1 -> (x0 (x0 x1)))) (\\x0 -> (x0+x0))) 11)")


-- Exercise: add open recursion to typecheck, so to make
-- it extensible. Add the Mul alternative, or booleans

main = do
       print tdyn1_eval
       print tdyn1_view
       print tx4_view

       print dt1
       print dt2
       print dt4
       print dt41
       print dt5
       print dt6
       print dt7
       print dt8
