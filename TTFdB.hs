-- * Essentially, Haskell98!
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Typed tagless-final interpreters for simply-typed lambda-calculus
-- * de Bruijn indices
-- based on the code accompanying the paper by
--   Jacques Carette, Oleg Kiselyov, and Chung-chieh Shan

module TTFdB where

-- * Abstracting over the final interpreter in IntroHOIF.hs

-- This class defines syntax (and its instances, semantics) 
-- of our language

-- I could've moved s and z into a separate ``class Var var_repr''
-- Symantics would then have a single form
-- v :: var_repr h a -> repr h a

class Symantics repr where
    int :: Int -> repr h Int                -- int literal
    add :: repr h Int -> repr h Int -> repr h Int

    z   :: repr (a,h) a			-- variables: z and s ... (s z)
    s   :: repr h a -> repr (any,h) a
    lam :: repr (a,h) b  -> repr h (a->b)
    app :: repr h (a->b) -> repr h a -> repr h b

-- * Like GADT-based, but in lower-case
-- * Like ExpSYM, but repr is of kind * -> * -> *
-- repr is parameterized by the environment (h) and the type
-- of the expression
-- * The types read like the rules of minimal logic
-- For example, z is the axiom stating that assuming A we can get A
-- lam is the inference rule: if assuming A we derive B,
-- then we can derive the implication A->B
-- * Type system of simply-typed lambda-calculus in Haskell98!
-- The signature of the class can be read off as the typing
-- rules for simply-typed lambda-calculus. But the code
-- is Haskell98! So, contrary to the common belief, we do not
-- need dependent types to express the type system of simply
-- typed lambda-calculus. Compare with Term.agda
-- * ``a way to write a typed fold function over a typed term.''
-- as one reviewer of our paper put it


-- * Sample terms and their inferred types
td1 = add (int 1) (int 2)
-- td1 :: (Symantics repr) => repr h Int

td2 = lam (add z z)
-- td2 :: (Symantics repr) => repr h (Int -> Int)

td2o = lam (add z (s z))
-- td2o :: (Symantics repr) => repr (Int, h) (Int -> Int)
-- the inferred type says td2o is open! Needs the env with Int

td3 = lam (add (app z (int 1)) (int 2))
-- td3 :: (Symantics repr) => repr h ((Int -> Int) -> Int)

-- Ill-typed terms are not expressible
-- * td2a = app (int 1) (int 2)
--     Couldn't match expected type `a -> b' against inferred type `Int'
--       Expected type: repr h (a -> b)
--       Inferred type: repr h Int
--     In the first argument of `app', namely `(int 1)'

-- * Embedding all and only typed terms of the object language
-- * in the typed metalanguage
-- Typed object terms are represented as typed Haskell terms


-- * //
-- * Typed and tagless evaluator
-- *  object term ==> metalanguage value

newtype R h a = R{unR :: h -> a}

instance Symantics R where
    int x     = R $ const x
    add e1 e2 = R $ \h -> (unR e1 h) + (unR e2 h)

    z     = R $ \(x,_) -> x
    s v   = R $ \(_,h) -> unR v h
    lam e = R $ \h -> \x -> unR e (x,h)
    app e1 e2 = R $ \h -> (unR e1 h) (unR e2 h)

eval e = unR e ()			-- Eval in the empty environment

-- * R is not a tag!
-- The expression with unR _looks_ like tag introduction and
-- elimination. But the function unR is *total*. There is no 
-- run-time error is possible at all -- and this fact is fully 
-- apparent to the compiler.
-- * R is a meta-circular interpreter
-- It runs each object-language operation by executing the corresponding
-- metalanguage operation.
-- * R never gets stuck: no variant types, no pattern-match failure
-- * Well-typed programs indeed don't go wrong!
-- * R is total
-- * The instance R is a constructive proof of type soundness
-- First of all, we see the type preservation (for object types)
-- for interpretations: interpretations preserve types.
-- Then we see progress: the interpreter does not get stuck.
-- So we reduced the problem of type soundness of the object language
-- (simply-typed lambda-calculus) to the type soundness of the
-- metalanguage.
-- * R _looks_ like a reader monad (but h varies)
-- R looks like a reader monad, but the type of the environment
-- varies.

-- Evaluate our test expressions
td1_eval = eval td1
-- 3

td2_eval = eval td2
-- td2_eval :: Int -> Int -- can't print
-- since td2_eval is a function taking Int, we can give it an Int
td2_eval' = eval td2 21
-- 42

-- td2o_eval = eval td2o
-- Can't evaluate the open term

td3_eval = eval td3
-- td3_eval :: (Int -> Int) -> Int

-- * //
-- Another interpreter

newtype S h a = S{unS :: [String] -> String}

instance Symantics S where
    int x     = S $ const $ show x
    add e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ "+" ++ unS e2 h ++ ")"

    z     = S $ \(x:_) -> x
    s v   = S $ \(_:h) -> unS v h
    lam e = S $ \h -> 
       let x = "x" ++ show (length h)
       in "(\\" ++ x ++ " -> " ++ unS e (x:h) ++ ")"
    app e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ " " ++ unS e2 h ++ ")"

-- Now this is almost the Reader monad. Why not fully?
-- The interpretation of lam is quite different from that in R
-- The environment is a regular, homogeneous list now
-- (see the rules 's' and 'z')

view :: S () a -> String -- Only closed terms can be viewed
view e = unS e []

td1_view = view td1
-- "(1+2)"

td2_view = view td2
-- "(\\x0 -> (x0+x0))"

td3_view = view td3
-- "(\\x0 -> ((x0 1)+2))"

-- We now finally see our terms in a useful form
-- Clearly, de Bruijn notation is not the most perspicuous
-- We now turn to HOAS

-- Exercise: implement the following extensions
{-

-- * //
-- Extensions of the language

-- * Multiplication
class MulSYM repr where
    mul :: repr r Int -> repr r Int -> repr r Int

-- * Booleans
class BoolSYM repr where
    bool :: Bool -> repr r Bool             -- bool literal
    if_ :: repr r Bool -> repr r a -> repr r a -> repr r a
    leq :: repr r Int -> repr r Int -> repr r Bool

-- * Fixpoint
class FixSYM repr where
    fix :: repr (a,h) a  -> repr h a

-- Logically, the signature of fix reads like nonsense
-- The extensions are independent

testpowfix () = lam {- x -} (
                  fix {- self -} (lam {- n -} (
                  let n = z; self = s z; x = s (s z)    
                  in  if_ (leq n (int 0)) (int 1)
                          (mul x (app self (add n (int (-1))))))))
testpowfix7 () = lam (app (app (testpowfix ()) z) (int 7))

rtestpw   = mkrtest testpowfix
rtestpw7  = mkrtest testpowfix7
rtestpw72 = mkrtest (\() -> app (testpowfix7 ()) (int 2)) -- 128

-- Another interpreter: it interprets each term to give its size
-- (the number of constructors)
-}

main = do
       print td1_eval
       print td2_eval'
       print td1_view
       print td2_view
       print td3_view

