-- | Term rewriting traversals.
module Plutonomy.Raw.Rewrite (
    -- * Rewrite
    rewrite,
    rewrite1,
    rewriteAll,
    rewriteWith,
    rewrite1With,
    rewriteAllWith,
    -- ** Bindings
    Bindings,
    TermWithArity (..),
    lookupBinding,
    bindingsEmpty,
    bindingsOnLet,
    bindingArity,
    isUnsaturatedApp,
    rewriteWithBindings,
    rewrite1WithBindings,
    -- * Folding of terms
    foldTerm,
) where

import Data.Kind (Type)
import Data.Bifunctor      (bimap)
import Data.Function       ((&))
import Data.Map.Strict     (Map)
import Subst               (Nat (..), NoCtx (..), Rename (..), Var (..), renameVar, weaken)

import qualified Data.Map.Strict as Map

import Plutonomy.MissingH
import Plutonomy.Name
import Plutonomy.Raw

-- $setup
-- >>> import Plutonomy
-- >>> import Subst
-- >>> import Data.Text (Text)
-- >>> import Control.Monad (forM_)
-- >>> import PlutusCore.Default (DefaultFun (..))
-- >>> import qualified Prettyprinter as PP
-- >>> let pp t = prettyRaw PP.pretty (t :: Raw Text Z)

-- | Rewrite trying once on each level.
--
-- >>> let term = "f" :@ "x"
-- >>> pp term
-- f x
--
-- >>> pp $ rewrite1 Just term
-- f x
--
--
rewrite1 :: forall a m. Ord a => (forall n. Raw a n -> Maybe (Raw a n)) -> Raw a m -> Raw a m
rewrite1 f = rewrite1With (const f) (\_ _ -> weaken) NoCtx

-- | Apply rewrites bottom up.
rewrite :: forall a m. Ord a => (forall n. Raw a n -> Maybe (Raw a n)) -> Raw a m -> Raw a m
rewrite f = rewriteWith (const f) (\_ _ -> weaken) NoCtx

grewrite
    :: forall a m ctx. (Rename ctx, Ord a)
    => (forall n. ctx n -> Raw a n -> Raw a n)                -- ^ local rewrite
    -> (forall n. Name -> Raw a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                                  -- ^ initial context
    -> Raw a m -> Raw a m
grewrite f' onLet = go where
    go :: forall n. ctx n -> Raw a n -> Raw a n
    go ctx x = f' ctx (recur ctx x)

    recur :: forall n. ctx n -> Raw a n -> Raw a n
    recur _ctx (Var x)      = Var x
    recur _ctx (Free x)     = Free x
    recur  ctx (Lam n t)    = Lam n (go (weaken ctx) t)
    recur  ctx (App g t)    = App (go ctx g) (go ctx t)
    recur  ctx (Force t)    = Force (go ctx t)
    recur  ctx (Delay t)    = Delay (go ctx t)
    recur _ctx (Constant c) = Constant c
    recur _ctx (Builtin b)  = Builtin b
    recur _ctx Error        = Error
    recur  ctx (Let n t s)  =
        let t' = go ctx t
        in Let n t' (go (onLet n t' ctx) s)

-- | Apply rewrites bottom up.
rewrite1With
    :: forall a m ctx. (Rename ctx, Ord a)
    => (forall n. ctx n -> Raw a n -> Maybe (Raw a n))        -- ^ local rewrite
    -> (forall n. Name -> Raw a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                                  -- ^ initial context
    -> Raw a m -> Raw a m
rewrite1With f = grewrite f' where
    f' :: forall n. ctx n -> Raw a n -> Raw a n
    f' ctx x = case f ctx x of
        Just x' -> x'
        Nothing -> x

-- | Apply rewrites bottom up. Rewrite each term until no rewrites apply.
--
-- Provide a context of bindings.
--
rewriteWith
    :: forall a m ctx. (Rename ctx, Ord a)
    => (forall n. ctx n -> Raw a n -> Maybe (Raw a n))        -- ^ local rewrite
    -> (forall n. Name -> Raw a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                                  -- ^ initial context
    -> Raw a m -> Raw a m
rewriteWith f = grewrite f' where
    f' :: forall n. ctx n -> Raw a n -> Raw a n
    f' ctx = iterateWhileJust (f ctx)

-- | Apply rewrites until a fixed point is reached.
--
-- @'rewriteAll' f = 'fixedpoint' ('rewrite' f)@
rewriteAll :: Ord a => (forall n. Raw a n -> Maybe (Raw a n)) -> Raw a m -> Raw a m
rewriteAll f = fixedpoint (rewrite f)

-- | Apply rewrites until a fixed point isrreached.
--
rewriteAllWith
    :: (Rename ctx, Ord a)
    => (forall n. ctx n -> Raw a n -> Maybe (Raw a n))        -- ^ local rewrite
    -> (forall n. Name -> Raw a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                                  -- ^ initial context
    -> Raw a m -> Raw a m
rewriteAllWith f onLet ctx = fixedpoint (rewriteWith f onLet ctx)

-------------------------------------------------------------------------------
-- Bindings
-------------------------------------------------------------------------------

-- | Map from variables to Terms (and their arities).
newtype Bindings a n = Bindings (Map (Var n) (TermWithArity a n))

rewriteWithBindings
    :: Ord a
    => (forall m. Bindings a m -> Raw a m -> Maybe (Raw a m))
    -> Raw a n
    -> Raw a n
rewriteWithBindings f = rewriteWith f bindingsOnLet bindingsEmpty

rewrite1WithBindings
    :: Ord a
    => (forall m. Bindings a m -> Raw a m -> Maybe (Raw a m))
    -> Raw a n
    -> Raw a n
rewrite1WithBindings f = rewrite1With f bindingsOnLet bindingsEmpty

-- | Term with arity.
--
-- The arity is not exact, but it is at least the given value.
type TermWithArity :: Type -> Nat -> Type
data TermWithArity a n = TermWithArity !Name !Int !(Raw a n)

bindingsEmpty :: Bindings m a
bindingsEmpty = Bindings Map.empty

bindingsOnLet :: Name -> Raw a m -> Bindings a m -> Bindings a ('S m)
bindingsOnLet n t (weaken -> Bindings ctx) =
    Bindings (Map.insert VZ (TermWithArity n a (weaken t)) ctx)
  where
    a = arity t

-- | Variable binding arity is at least the returned value.
bindingArity :: Bindings a n -> Var n ->  Int
bindingArity ctx x = case lookupBinding ctx x of
    Just (TermWithArity _n a _t) -> a
    Nothing                      -> 0

isUnsaturatedApp :: Bindings a n -> Raw a n -> Bool
isUnsaturatedApp ctx t
    | (Var f, args) <- peelApp t
    , a <- bindingArity ctx f
    , length args < a
    = True

    | otherwise
    = False

lookupBinding :: Bindings a n -> Var n -> Maybe (TermWithArity a n)
lookupBinding (Bindings ctx) x = Map.lookup x ctx

instance Rename (TermWithArity a) where
    r <@> TermWithArity n a t = TermWithArity n a (r <@> t)

instance Rename (Bindings a) where
    r <@> Bindings ctx = Bindings $ Map.fromList . map (bimap (renameVar r) (r <@>)) . Map.toList $ ctx

-- Arity of a binding.
--
-- >>> arity $ lam_ "x" "x"
-- 1
--
-- >>> arity "free"
-- 0
--
arity :: Raw a n -> Int
arity = go 0 where
    go :: Int -> Raw a n -> Int
    go !acc (Lam _ t) = go (acc + 1) t
    go  acc (Delay t) = go (acc + 1) t
    go  acc _         = acc

-------------------------------------------------------------------------------
-- Fold
-------------------------------------------------------------------------------

-- | Fold over term and all of its subterms.
foldTerm :: forall s m a. Semigroup s => (forall n. Raw a n -> s) -> Raw a m -> s
foldTerm g = go where
    go :: Raw a n -> s
    go term = g term & case term of
        Var {}      -> id
        Free {}     -> id
        Builtin {}  -> id
        Constant {} -> id
        Error {}    -> id

        Lam _n t    -> \acc -> acc <> go t
        App f t     -> \acc -> acc <> go f <> go t
        Force t     -> \acc -> acc <> go t
        Delay t     -> \acc -> acc <> go t
        Let _n t s  -> \acc -> acc <> go t <> go s
