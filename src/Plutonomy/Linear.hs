-- | This module is currently unused.
module Plutonomy.Linear (
    isLinear,
    isAffine,
) where

import Control.Applicative       (liftA2)
import Control.Monad.Trans.State (State, evalState, runState, state)
import Subst                     (Nat (S), Var (..))

import Plutonomy.Raw

-- $setup
-- >>> import Plutonomy
-- >>> import Subst
-- >>> import Data.Text (Text)
-- >>> import qualified Prettyprinter as PP
-- >>> let pp t = prettyRaw PP.pretty (t :: Raw Text Z)

-- | Whether term is linear.
--
-- >>> isLinear $ lam_ "x" "x"
-- True
--
-- >>> isLinear $ lam_ "x" $ lam_ "y" "x"
-- False
--
-- >>> isLinear $ lam_ "x" $ "f" :@ "x" :@ "x"
-- False
--
-- >>> isLinear $ lam_ "x" "x" :@ "freeVar"
-- True
--
-- >>> isLinear $ let_ "x" "freeVar" "x"
-- True
--
isLinear :: Raw a n -> Bool
isLinear = isLinear' False

-- | Whether term is affine
--
-- >>> isAffine $ lam_ "x" "x"
-- True
--
-- >>> isAffine $ lam_ "x" $ lam_ "y" "x"
-- True
--
-- >>> isAffine $ lam_ "x" $ "f" :@ "x" :@ "x"
-- False
--
-- >>> isAffine $ lam_ "x" "x" :@ "freeVar"
-- True
--
-- >>> isAffine $ let_ "x" "freeVar" "x"
-- True
--
isAffine :: Raw a n -> Bool
isAffine = isLinear' True

isLinear' :: Bool -> Raw a n -> Bool
isLinear' affine term = evalState (go term) Frees where
    go :: Raw a n -> State (Uses n) Bool
    go (Var x) = state $ \ctx -> case use x ctx of
        Nothing   -> (False, ctx)
        Just ctx' -> (True, ctx')

    go (Lam _n t) = state $ \ctx ->
        let (res, ctx') = runState (go t) (Cons1 ctx)
        in case ctx' of
              Cons0 ctx'' -> (res, ctx'')
              Cons1 ctx'' -> (affine && res, ctx'')
              Frees       -> (False, ctx) -- shouldn't happen.

    go (Let _n t s) = liftA2 (&&) (go t) $ state $ \ctx ->
        let (res, ctx') = runState (go s) (Cons1 ctx)
        in case ctx' of
              Cons0 ctx'' -> (res, ctx'')
              Cons1 ctx'' -> (affine && res, ctx'')
              Frees       -> (False, ctx) -- shouldn't happen.

    go Free {}     = pure True
    go Constant {} = pure True
    go Builtin {}  = pure True
    go Error       = pure True

    go (App f x)   = liftA2 (&&) (go f) (go x)
    go (Delay t)   = go t
    go (Force t)   = go t

data Uses (n :: Nat) where
    Frees :: Uses n
    Cons0 :: Uses n -> Uses (S n)
    Cons1 :: Uses n -> Uses (S n)

use :: Var n -> Uses n -> Maybe (Uses n)
use _      Frees     = Just Frees
use VZ     (Cons0 _) = Nothing
use VZ     (Cons1 n) = Just (Cons0 n)
use (VS i) (Cons0 n) = Cons0 <$> use i n
use (VS i) (Cons1 n) = Cons1 <$> use i n
