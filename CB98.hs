-- Haskell98!

-- Embedding a higher-order domain-specific language (simply-typed
-- lambda-calculus with constants) with a selectable evaluation order:
-- Call-by-value, call-by-name, call-by-need in the same Final Tagless framework
-- This is the Haskell98 version of the code CB.hs located in the
-- same directory as this file

module CB98 where

import Data.IORef
import Control.Monad
import Control.Monad.Trans

-- The (higher-order abstract) syntax of our DSL
type Arr exp a b = exp a -> exp b
class EDSL exp where
     lam :: (exp a -> exp b) -> exp (Arr exp a b)
     app :: exp (Arr exp a b) -> exp a -> exp b

     int :: Int -> exp Int		-- Integer literal
     add :: exp Int -> exp Int -> exp Int
     sub :: exp Int -> exp Int -> exp Int

-- A convenient abbreviation
let_ :: EDSL exp => exp a -> (exp a -> exp b) -> exp b
let_ x y = (lam y) `app` x

-- A sample EDSL term
t :: EDSL exp => exp Int
t = (lam $ \x -> let_ (x `add` x)
                      $ \y -> y `add` y) `app` int 10

-- Interpretation of EDSL expressions as values of the host language (Haskell)
-- An EDSL expression of type a is interpreted as a Haskell value
-- of the type SName m a, SValue m a or SLazy m a, where
-- m is a Monad (the parameter of the interpretation).

newtype SName m a = SN { unSN :: m a }

-- Could be automatically derived by GHC. But we stick to Haskell98
instance Monad m => Monad (SName m) where
    return = SN . return
    m >>= f = SN $ unSN m >>= unSN . f
instance MonadIO m => MonadIO (SName m) where
    liftIO = SN . liftIO


-- Call-by-name

instance MonadIO m => EDSL (SName m) where
  int = return
  add x y = do a <- x
	       b <- y
	       liftIO $ putStrLn "Adding"
	       return (a + b)
  sub x y = do a <- x
	       b <- y
	       liftIO $ putStrLn "Subtracting"
	       return (a - b)
  lam f   = return f
  app x y = x >>= ($ y)


-- Tests


runName :: SName m a -> m a
runName x = unSN x

-- The addition (x `add` x) is performed twice because y is bound
-- to a computation, and y is evaluated twice
t0SN = runName t >>= print
{-
Adding
Adding
Adding
40
-}

-- A more elaborate example
t1 :: EDSL exp => exp Int
t1 = (lam $ \x -> let_ (x `add` x) 
                  $ \y -> lam $ \z -> 
                  z `add` (z `add` (y `add` y))) `app` (int 10 `sub` int 5) 
                                                 `app` (int 20 `sub` int 10)

t1SN = runName t1 >>= print
{-
*CB> t1SN
Subtracting
Subtracting
Subtracting
Subtracting
Adding
Subtracting
Subtracting
Adding
Adding
Adding
Adding
40
-}

-- A better example
t2 :: EDSL exp => exp Int
t2 = (lam $ \z -> lam $ \x -> let_ (x `add` x)
                      $ \y -> y `add` y) `app` (int 100 `sub` int 10)
                                         `app` (int 5 `add` int 5)

-- The result of subtraction was not needed, and so it was not performed
-- OTH, (int 5 `add` int 5) was computed four times
t2SN = runName t2 >>= print
{-
*CB> t2SN
Adding
Adding
Adding
Adding
Adding
Adding
Adding
40
-}

-- Call-by-value

newtype SValue m a = SV { unSV :: m a }

-- Could be automatically derived by GHC. 
instance Monad m => Monad (SValue m) where
    return = SV . return
    m >>= f = SV $ unSV m >>= unSV . f
instance MonadIO m => MonadIO (SValue m) where
    liftIO = SV . liftIO

-- We reuse most of EDSL (SName) except for lam
vn :: SValue m x -> SName m x
vn = SN . unSV
nv :: SName m x -> SValue m x
nv = SV . unSN

instance MonadIO m => EDSL (SValue m) where
    int = nv . int
    add x y = nv $ add (vn x) (vn y)
    sub x y = nv $ sub (vn x) (vn y)
    -- Easier to write it rather than to change the label and then
    -- invoke SName's app
    app x y = x >>= ($ y)

    -- This is the only difference between CBN and CBV:
    -- lam first evaluates its argument, no matter what
    -- This is the definition of CBV after all
    -- lam f   = return (\x -> (f . return) =<< x)
    -- or, in the pointless notation suggested by Jacques Carette
    lam f   = return (f . return =<<)

runValue :: SValue m a -> m a
runValue x = unSV x

-- We now evaluate the previously written tests t, t1, t2
-- under the new interpretation

t0SV = runValue t >>= print
{-
*CB> t0SV
Adding
Adding
40
-}

t1SV = runValue t1 >>= print
{-
*CB> t1SV
Subtracting
Adding
Subtracting
Adding
Adding
Adding
40
-}

-- Although the result of subs-traction was not needed, it was still performed
-- OTH, (int 5 `add` int 5) was computed only once
t2SV = runValue t2 >>= print
{-
*CB> t2SV
Subtracting
Adding
Adding
Adding
40
-}


-- Call-by-need

share :: MonadIO m => m a -> m (m a)
share m = do
	  r <- liftIO $ newIORef (False,m)
	  let ac = do
		   (f,m) <- liftIO $ readIORef r
		   if f then m
		      else do
			   v <- m
			   liftIO $ writeIORef r (True,return v)
			   return v
	  return ac

newtype SLazy m a = SL { unSL :: m a }

-- Could be automatically derived by GHC. 
instance Monad m => Monad (SLazy m) where
    return = SL . return
    m >>= f = SL $ unSL m >>= unSL . f
instance MonadIO m => MonadIO (SLazy m) where
    liftIO = SL . liftIO

ln :: SLazy m x -> SName m x
ln = SN . unSL
nl :: SName m x -> SLazy m x
nl = SL . unSN
-- We reuse most of EDSL (SName) except for lam
instance MonadIO m => EDSL (SLazy m) where
    int = nl . int
    add x y = nl $ add (ln x) (ln y)
    sub x y = nl $ sub (ln x) (ln y)
    -- Easier to write it rather than change the label and then
    -- invoke SName's app
    app x y = x >>= ($ y)

    -- This is the only difference between CBN and CBNeed
    -- lam shares its argument, no matter what
    -- This is the definition of CBNeed after all
    -- lam f           = return (\x -> f =<< share x)
    -- Or, in the pointless notation
    lam f           = return ((f =<<) . share)


runLazy :: SLazy m a -> m a
runLazy x = unSL x

-- We now evaluate the previously written tests t, t1, t2
-- under the new interpretation

-- Here, Lazy is just as efficient as CBV
t0SL = runLazy t  >>= print
{-
*CB> t0SL
Adding
Adding
40
-}

-- Ditto
t1SL = runLazy t1 >>= print
{-
*CB> t1SL
Subtracting
Subtracting
Adding
Adding
Adding
Adding
40
-}

-- Now, Lazy is better than both CBN and CBV: subtraction was not needed,
-- and it was not performed.
-- All other expressions were needed, and evaluated once.
t2SL = runLazy t2 >>= print
{-
*CB> t2SL
Adding
Adding
Adding
40
-}