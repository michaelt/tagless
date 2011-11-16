-- * Essentially, Haskell98!
{-# LANGUAGE NoMonomorphismRestriction #-}

-- * Typed tagless-final interpreters for PCF
-- * Higher-order abstract syntax
-- based on the code accompanying the paper by
--   Jacques Carette, Oleg Kiselyov, and Chung-chieh Shan

module TTF where

-- The language is simply-typed lambda-calculus with fixpoint and
-- constants. It is essentially PCF.
-- The language is just expressive enough for the power function.
-- We define the language by parts, to emphasize modularity.
-- The core plus the fixpoint is the language described in the paper
--    Hongwei Xi, Chiyan Chen, Gang Chen
--    Guarded Recursive Datatype Constructors, POPL2003
-- which is used to justify GADTs.


-- * Core language
class Symantics repr where
    int :: Int  -> repr Int              -- int literal
    add :: repr Int  -> repr Int -> repr Int

    lam :: (repr a -> repr b) -> repr (a->b)
    app :: repr (a->b) -> repr a -> repr b

-- * Like ExpSYM, but repr is of kind * -> *
-- repr is parameterized by the type of the expression
-- * The types read like the minimal logic in 
-- * Gentzen-style natural deduction
-- * Type system of simply-typed lambda-calculus in Haskell98!

-- * Sample terms and their inferred types
-- They do look better now.
th1 = add (int 1) (int 2)
-- th1 :: (Symantics repr) => repr Int

th2 = lam (\x -> add x x)
-- th2 :: (Symantics repr) => repr (Int -> Int)

th3 = lam (\x -> add (app x (int 1)) (int 2))
-- th3 :: (Symantics repr) => repr ((Int -> Int) -> Int)


-- * th2o = lam (\x -> add x y)
-- th2o is not accepted: open terms are simply not
-- expressible in HOAS


-- * //
-- * Typed and tagless interpreter

newtype R a = R{unR :: a}
instance Show a => Show (R a) where
  show (R a) = show a
instance Symantics R where
    int x     = R x
    add e1 e2 = R $ unR e1 + unR e2

    lam f     = R $ unR . f . R
    app e1 e2 = R $ (unR e1) (unR e2)

-- * R is not a tag! It is a newtype
-- The expression with unR _looks_ like tag introduction and
-- elimination. But the function unR is *total*. There is no 
-- run-time error is possible at all -- and this fact is fully 
-- apparent to the compiler.
-- Furthermore, at run-time, (R x) is indistinguishable from x
-- * R is a meta-circular interpreter
-- This is easier to see now. So, object-level addition is
-- _truly_ the metalanguage addition. Needless to say, that is
-- efficient.
-- * R never gets stuck: no pattern-matching of any kind
-- * R is total

eval e = unR e

th1_eval = eval th1
-- 3

th2_eval = eval th2
-- th2_eval :: Int -> Int
-- We can't print a function, but we can apply it

th2_eval' = eval th2 21
-- 42

th3_eval = eval th3
-- th3_eval :: (Int -> Int) -> Int


-- * //
-- Another interpreter

type VarCounter = Int
newtype S a = S{unS:: VarCounter -> String}

instance Symantics S where
    int x     = S $ const $ show x
    add e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ "+" ++ unS e2 h ++ ")"

    lam e = S $ \h -> 
       let x = "x" ++ show h
       in "(\\" ++ x ++ " -> " ++ 
            unS (e (S $ const x)) (succ h) ++ ")"
    app e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ " " ++ unS e2 h ++ ")"

-- The major difference from TTFdb is the interpretation
-- of lam

view e = unS e 0

th1_view = view th1
-- "(1+2)"

th2_view = view th2
-- "(\\x0 -> (x0+x0))"

th3_view = view th3
-- "(\\x0 -> ((x0 1)+2))"

-- * The crucial role of repr being a type constructor
-- rather than just a type. It lets some information about
-- object-term representation through (the type) while
-- keeping the representation itself hidden.


-- * //
-- * Extensions of the language

-- * Multiplication
class MulSYM repr where
    mul :: repr Int -> repr Int -> repr Int

-- * Booleans
class BoolSYM repr where
    bool :: Bool -> repr Bool             -- bool literal
    leq :: repr Int -> repr Int -> repr Bool
    if_ :: repr Bool -> repr a -> repr a -> repr a

-- * Fixpoint
class FixSYM repr where
    fix :: (repr a -> repr a)  -> repr a

-- Logically, the signature of fix reads like nonsense
-- * http://xkcd.com/704/

-- * Extensions are independent of each other

-- The main power
-- Looks like Scheme, doesn't it?
-- We can define suitable infix operators however.

-- The inferred type of pow shows all the extensions in action
tpow  = lam (\x -> fix (\self -> lam (\n ->
                        if_ (leq n (int 0)) (int 1)
                            (mul x (app self (add n (int (-1))))))))
-- tpow :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) =>
--         repr (Int -> Int -> Int)

tpow7 = lam (\x -> app (app tpow x) (int 7))
tpow72 = app tpow7 (int 2)
-- tpow72 :: (Symantics repr, BoolSYM repr, MulSYM repr, FixSYM repr) => 
-- repr Int

-- * //
-- * Extending the R interpreter

instance MulSYM R where
    mul e1 e2 = R $ unR e1 * unR e2

instance BoolSYM R where
    bool b    = R b
    leq e1 e2 = R $ unR e1 <= unR e2
    if_ be et ee = R $ if unR be then unR et else unR ee 

instance FixSYM R where
    fix f = R $ fx (unR . f . R) where fx f = f (fx f)

-- Again, the extensions are independent

tpow_eval = eval tpow
-- tpow_eval :: Int -> Int -> Int

tpow72_eval = eval tpow72
-- 128

-- * //
-- * Extending the S interpreter

-- Only the case of fix is interesting (and perhaps, of if_)

instance MulSYM S where
    mul e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ "*" ++ unS e2 h ++ ")"

instance BoolSYM S where
    bool x     = S $ const $ show x
    leq e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ "<=" ++ unS e2 h ++ ")"
    if_ be et ee = S $ \h ->
       unwords["(if", unS be h, "then", unS et h, "else", unS ee h,")"]

instance FixSYM S where
    fix e = S $ \h -> 
       let self = "self" ++ show h
       in "(fix " ++ self ++ "." ++ 
            unS (e (S $ const self)) (succ h) ++ ")"

tpow_view = view tpow
-- "(\\x0 -> (fix self1.(\\x2 -> (if (x2<=0) then 1 else (x0*(self1 (x2+-1))) ))))"

-- Other interpreters are possible: C (staging), L and P (partial evaluation)
-- Refer to the slide with the contributions of the paper

{-
-- Another interpreter: it interprets each term to give its size
-- (the number of constructors)
-}

main = do
       print th1_eval
       print th2_eval'

       print th1_view
       print th2_view
       print th3_view

       print tpow72_eval
       print tpow_view
