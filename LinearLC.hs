{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- * Typed tagless-final interpreters for 
-- * Linear Lambda Calculus
-- * de Bruijn indices

-- Linear lambda-calculus: each bound variable
-- is referenced exactly once.
-- Application: natural language semantics:
-- (see for example, works by Michael Moortgat)
-- In particular, linear lambda calculi are extensively
-- used in Abstract Categorial Grammars.

-- The following code would look better in ML: we can declare
-- types F and U in a signature. They will be assumed distinct.
-- Yet an implementation of the signature may conflate
-- the F and U types; therefore, we can use the interpreter
-- for the ordinary lambda calculus.
-- Alas, this approach doesn't work for Haskell:
-- If we use associated types to model type-class
-- local types F and U, the type checker does not
-- consider them necessarily distinct and generates equality
-- constraint. That breaks the abstraction!
-- Terms like tl2 below would not be rejected.

module LinearLC where


newtype F a = F a			-- actual variable
data U = Used

-- This semantics assumes that all values (that is, substitutable
-- things) are closed terms. This is the case in CBV or CBN
-- calculi, which never evaluate under lambda.
-- Therefore, we do not qualify the types of values by the env
-- Otherwise, we have to qualify each type such as Int or
-- a with its env.
-- For the unextended linear lambda calculus below, we don't
-- need to make this restriction as substitution of linear terms
-- into linear terms doesn't violate the linearity. But that
-- property is not stated syntactically below.
-- Stating it syntactically does seem possible, but the
-- code becomes quite more complex.
class LSymantics repr where
    int :: Int -> repr hi hi Int
    add :: repr hi h Int -> repr h ho Int -> repr hi ho Int

    z   :: repr (F a,h) (U,h) a
    s   :: repr hi ho a -> repr (any,hi) (any,ho) a
    app :: repr hi h (a->b) -> repr h ho a -> repr hi ho b

-- The reason we separate out 'lam' is to expose the type variables
-- hi and ho in the class head. A particular instance might be able to attach
-- constraints to hi and ho. The instance for the R interpreter
-- indeed attaches the HiHo constraint.
class LinearL repr hi ho where
    lam :: repr (F a,hi) (U,ho) b  -> repr hi ho (a->b)

-- * Sample terms and their inferred types
tl1 = add (int 1) (int 2)
-- tl1 :: (LSymantics repr) => repr hi hi Int

-- * tl2 = lam (add z z)
-- This term is not linear
--     Couldn't match expected type `U' against inferred type `F a'
--       Expected type: repr (U, hi) (U, ho) Int
--       Inferred type: repr (F a, h) (U, h) a
--     In the second argument of `add', namely `z'
--     In the first argument of `lam', namely `(add z z)'

tl2o = lam (add z (s z))
-- tl2o :: (LSymantics repr) => repr (F Int, h) (U, h) (Int -> Int)
-- The term is open. It can still be written

-- * tlk = lam (lam z)
-- The outer lam's argument is not consumed
--     Couldn't match expected type `F a' against inferred type `U'
--       Expected type: repr (F a1, (F a, hi)) (U, (U, ho)) b
--       Inferred type: repr (F a1, (U, hi)) (U, (U, hi)) a1
--     In the first argument of `lam', namely `z'
--     In the first argument of `lam', namely `(lam z)'


tl3 = lam (add (app z (int 1)) (int 2))
-- tl3 :: (LSymantics repr) => repr hi hi ((Int -> Int) -> Int)

tl4 = lam (lam (add z (s z)))
-- tl4 :: (LSymantics repr) => repr hi hi (Int -> Int -> Int)

tl5 = lam (app (lam z) z)
-- tl5 :: (LSymantics repr) => repr hi hi (a -> a)


-- * //
-- * Typed and tagless evaluator
-- *  object term ==> metalanguage value

newtype R hi ho a = R{unR :: hi -> (a,ho)}

instance LSymantics R where
    int x     = R $ \hi -> (x,hi)
    add e1 e2 = R $ \hi ->
		      let (v1,h)  = unR e1 hi
		          (v2,ho) = unR e2 h
		      in (v1+v2,ho)    

    z     = R $ \(F x,h) -> (x,(Used,h))
    s v   = R $ \(any,hi) -> 
                  let (x,ho) = unR v hi
		  in (x,(any,ho))

    app e1 e2 = R $ \hi ->
		      let (v1,h)  = unR e1 hi
		          (v2,ho) = unR e2 h
		      in (v1 v2,ho)    

-- * //
-- * Interpreting lam is quite more different
-- Why?
-- Why the simple approach does not work?
-- We need to produce ho when the lambda-form is produced,
-- not when it is applied. But ho of the lambda-form
-- includes the ho for the body of lambda. The latter is
-- the result of evaluating the body; but we get to evaluate
-- the body of the lambda only when the lambda-form is applied.
-- But we need that ho now. Fortunately, types are enough to
-- produce ho. That's the purpose for the type class HiHo.

class HiHo hi ho where
    hiho :: hi -> ho

instance HiHo () () where
    hiho = id

instance HiHo hi ho => HiHo (F a,hi) (F a,ho) where
    hiho (x,hi) = (x,hiho hi)

instance HiHo hi ho => HiHo (F a,hi) (U,ho) where
    hiho (x,hi) = (Used,hiho hi)

instance HiHo hi ho => LinearL R hi ho where
    lam e = R $ \hi -> (f hi, hiho hi)
     where f hi x = let (v,_) = unR e (F x,hi)
		    in v

-- The implementation of lam shows that the value of lam, which is
-- f hi, is the closure of the (input) environment in which
-- lam was produced.

eval e = fst $ unR e ()			-- Eval in the empty environment

tl1_eval = eval tl1
-- 3

-- * tl2o_eval = eval tl2o
-- Cannot evaluate an open term
--     Couldn't match expected type `()'
--            against inferred type `(F Int, h)'
--       Expected type: R () b a
--       Inferred type: R (F Int, h) (U, h) (Int -> Int)
--     In the first argument of `eval', namely `tl2o'

-- tl3 = lam (add (app z (int 1)) (int 2))
tl3_eval = eval tl3
-- tl3_eval :: (Int -> Int) -> Int

tl3_eval' = tl3_eval succ
-- 4

tl4_eval = eval tl4
-- tl4_eval :: Int -> Int -> Int

tl4_eval' = tl4_eval 19 35
-- 54

tl5_eval = eval tl5
-- tl5_eval :: a -> a

tl5_eval' = tl5_eval True
-- True


-- * //
-- Another interpreter
-- * Literally the same as Symantics.S
-- Although I later decided to print linear lambdas as \!x -> ...

newtype S hi ho a = S{unS :: [String] -> String}

instance LSymantics S where
    int x     = S $ const $ show x
    add e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ "+" ++ unS e2 h ++ ")"

    z     = S $ \(x:_) -> x
    s v   = S $ \(_:h) -> unS v h

    app e1 e2 = S $ \h -> 
      "(" ++ unS e1 h ++ " " ++ unS e2 h ++ ")"

instance LinearL S hi ho where
    lam e = S $ \h -> 
       let x = "x" ++ show (length h)
       in "(\\!" ++ x ++ " -> " ++ unS e (x:h) ++ ")"

view :: S () () a -> String
view e = unS e []

tl1_view = view tl1
-- "(1+2)"

-- * tl2o_view = view tl2o
-- Open terms can't be viewed

tl3_view = view tl3
-- "(\\!x0 -> ((x0 1)+2))"

tl4_view = view tl4
-- "(\\!x0 -> (\\!x1 -> (x1+x0)))"

tl5_view = view tl5
-- "(\\!x0 -> ((\\!x1 -> x1) x0))"

-- * Exercise: add an affine lambda

-- * //
-- * Extension: the ordinary lam

newtype G a = G a

class GenL repr hi ho where
    glam :: repr (G a,hi) (G a,ho) b  -> repr hi ho (a->b)

class GZ repr where
    gz :: repr (G a,hi) (G a,hi) a

-- Now, non-linear terms like tl2 and the K combinator
-- become expressible

tg2 = glam (add gz gz)
-- tg2 :: (GZ repr, LSymantics repr, GenL repr hi hi) => 
--        repr hi hi (Int -> Int)

-- The K combinator is expressible in two ways

tgk = glam (glam gz)
-- tgk :: (GZ repr, GenL repr (G a1, hi) (G a1, hi), GenL repr hi hi) =>
--        repr hi hi (a1 -> a -> a)

tgk' = glam (lam z)
-- tgk' :: (LSymantics repr,
--          LinearL repr (G a1, hi) (G a1, hi),
--          GenL repr hi hi) =>
--         repr hi hi (a1 -> a -> a)

-- Mixing linear and non-linear lambdas
tg4 = glam (lam (add (s gz) (add z (s gz))))
-- tg4 :: (GZ repr,
--         LSymantics repr,
--         LinearL repr (G Int, hi) (G Int, hi),
--         GenL repr hi hi) =>
--        repr hi hi (Int -> Int -> Int)

tg5 = glam (app (lam z) gz)

-- The following does not type-check, although it is `morally correct'
-- Syntactically, the term is non-linear!
-- The linear calculus without extensions did not have
-- the problem of being too conservative: a function
-- cannot avoid using its argument.
-- So, a term that is syntactically linear is semantically
-- linear, and vice versa.
-- It is only when we added general lambdas that the calculus
-- became conservative: a function like the K combinator
-- can disregard its argument expression. So, 
-- a term that is syntactically non-linear may still
-- end up using each argument expression once.
-- In general, we have to evaluate it to see it.
-- * tg6 = lam ((tgk `app` z) `app` (add (int 1) z))

tg71 = glam (app gz (lam z))
-- tg71::        repr hi hi (((a -> a) -> b) -> b)

-- the following are OK because we never evaluate under lambda
-- All values are always closed terms. Therefore,
-- even though a non-linear function may replicate its
-- arguments, it replicates values -- never variables
tg72 = lam (glam (app gz (s z)))
-- tg72:: repr hi hi (a -> (a -> b) -> b)

tg73 = glam (lam (app (s gz) z))
-- repr hi hi ((a -> b) -> a -> b)

tg74 = lam (lam (app (s z) z))
-- repr hi hi ((a -> b) -> a -> b)

-- * //
-- * We extend the interpreters

instance HiHo hi ho => GenL R hi ho where
    glam e = R $ \hi -> (f hi, hiho hi)
     where f hi x = let (v,_) = unR e (G x,hi)
		    in v
instance GZ R where
    gz     = R $ \(G x,h) -> (x,(G x,h))

instance HiHo hi ho => HiHo (G a,hi) (G a,ho) where
    hiho (x,hi) = (x,hiho hi)

tg2_eval = eval tg2 27
-- 54

tgk_eval = eval tgk "abc" "cde"

tgk'_eval = eval tgk' "abc" "cde"

tg4_eval = eval tg4 20 2
-- 42

tg5_eval = eval tg5 True
-- True

tg72_eval = eval tg72 4 succ
--5

tg73_eval = eval tg73 succ 4
-- 5

tg74_eval = eval tg74 succ 4
-- 5

-- * //
-- * We extend the S interpreter

instance GZ S where
    gz     = S $ \(x:_) -> x

instance GenL S hi ho where
    glam e = S $ \h -> 
       let x = "y" ++ show (length h)
       in "(\\" ++ x ++ " -> " ++ unS e (x:h) ++ ")"


tg2_view = view tg2
-- "(\\y0 -> (y0+y0))"

tgk_view = view tgk
-- "(\\y0 -> (\\y1 -> y1))"

tgk'_view = view tgk'
-- "(\\y0 -> (\\!x1 -> x1))"

tg4_view = view tg4
-- "(\\y0 -> (\\!x1 -> (y0+(x1+y0))))"

tg5_view = view tg5
-- "(\\y0 -> ((\\!x1 -> x1) y0))"

main = do
       print tl1_eval
       print tl3_eval'
       print tl4_eval'
       print tl5_eval'

       print tl1_view
       print tl3_view
       print tl4_view
       print tl5_view

       print tg2_eval
       print tgk_eval
       print tgk'_eval
       print tg4_eval
       print tg5_eval

       print tg2_view
       print tgk_view
       print tgk'_view
       print tg4_view
       print tg5_view
