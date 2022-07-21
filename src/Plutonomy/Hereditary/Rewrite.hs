module Plutonomy.Hereditary.Rewrite (
    -- * Rewrite
    rewrite,
    rewrite1,
    rewriteAll,
    rewriteWith,
    rewrite1With,
    rewriteAllWith,
    -- ** Definitions
    Definitions,
    DefnWithArity (..),
    definitionLookup,
    definitionsOnLet,
    definitionArity,
    isUnsaturatedApp,
    rewriteWithDefinitions,
    rewrite1WithDefinitions,
) where

import Data.Bifunctor  (bimap)
import Data.Kind       (Type)
import Data.Map.Strict (Map)
import Subst           (Nat (..), NoCtx (..), Rename (..), Var (..), bump, renameVar, weaken)

import qualified Data.Map.Strict as Map

import Plutonomy.Hereditary
import Plutonomy.MissingH
import Plutonomy.Name

-------------------------------------------------------------------------------
-- General rewrit
-------------------------------------------------------------------------------

grewrite
    :: forall a m ctx. Rename ctx
    => (forall n. ctx n -> Term a n -> Term a n)               -- ^ rewrite
    -> (forall n. Name -> Defn a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                                   -- ^ initial context
    -> Term a m -> Term a m
grewrite f' onLet = goTerm where
    goTerm :: forall n. ctx n -> Term a n -> Term a n
    goTerm ctx x = f' ctx (rwTerm ctx x)

    goDefn :: forall n. ctx n -> Defn a n -> Defn a n
    goDefn  ctx (Lam n t)      = Lam n (goTerm (weaken ctx) t)
    goDefn  ctx (Delay t)      = Delay (goTerm ctx t)
    goDefn _ctx (Constant c)   = Constant c
    goDefn  ctx (Neutral h sp) = Neutral h (goSpine ctx sp)

    goSpine :: forall n. ctx n -> Spine a n -> Spine a n
    goSpine ctx                = fmap (goElim ctx)

    goElim :: forall n. ctx n -> Elim a n -> Elim a n
    goElim _ctx Force          = Force
    goElim  ctx (App t)        = App (goTerm ctx t)
    goElim _ctx Fst            = Fst
    goElim _ctx Snd            = Snd

    rwTerm :: forall n. ctx n -> Term a n -> Term a n
    rwTerm _ctx Error          = Error
    rwTerm  ctx (Defn d)       = Defn (goDefn ctx d)
    rwTerm  ctx (Let n t s)    = goLet ctx n (goTerm ctx (Defn t)) s

    goLet :: forall n. ctx n -> Name -> Term a n -> Term a ('S n) -> Term a n
    goLet _ctx _ t            Var0 = t
    goLet _ctx _ Error        _    = Error
    goLet  ctx n  (Defn t)    r    = mkLet' n t $ goTerm (onLet n t ctx) r
    goLet  ctx n' (Let n t s) r    = mkLet' n t $ goLet  (onLet n t ctx) n' s (bump r)

-------------------------------------------------------------------------------
-- Specialized rewrites
-------------------------------------------------------------------------------

-- | Apply rewrites bottom up.
rewrite1With
    :: forall a m ctx. (Rename ctx, Ord a)
    => (forall n. ctx n -> Term a n -> Maybe (Term a n))   -- ^ local rewrite
    -> (forall n. Name -> Defn a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                               -- ^ initial context
    -> Term a m -> Term a m
rewrite1With f = grewrite f' where
    f' :: forall n. ctx n -> Term a n -> Term a n
    f' ctx x = case f ctx x of
        Just x' -> x'
        Nothing -> x

-- | Apply rewrites bottom up. Rewrite each term until no rewrites apply.
--
-- Provide a context of bindings.
--
rewriteWith
    :: forall a m ctx. (Rename ctx, Ord a)
    => (forall n. ctx n -> Term a n -> Maybe (Term a n))   -- ^ local rewrite
    -> (forall n. Name -> Defn a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                               -- ^ initial context
    -> Term a m -> Term a m
rewriteWith f = grewrite f' where
    f' :: forall n. ctx n -> Term a n -> Term a n
    f' ctx = iterateWhileJust (f ctx)

-- | Apply rewrites until a fixed point isrreached.
--
rewriteAllWith
    :: (Rename ctx, Ord a)
    => (forall n. ctx n -> Term a n -> Maybe (Term a n))   -- ^ local rewrite
    -> (forall n. Name -> Defn a n -> ctx n -> ctx (S n))  -- ^ let
    -> ctx m                                               -- ^ initial context
    -> Term a m -> Term a m
rewriteAllWith f onLet ctx = fixedpoint (rewriteWith f onLet ctx)

rewrite1 :: forall a m. Ord a => (forall n. Term a n -> Maybe (Term a n)) -> Term a m -> Term a m
rewrite1 f = rewrite1With (const f) (\_ _ -> weaken) NoCtx

-- | Apply rewrites bottom up.
rewrite :: forall a m. Ord a => (forall n. Term a n -> Maybe (Term a n)) -> Term a m -> Term a m
rewrite f = rewriteWith (const f) (\_ _ -> weaken) NoCtx

-- | Apply rewrites until a fixed point is reached.
--
-- @'rewriteAll' f = 'fixedpoint' ('rewrite' f)@
rewriteAll :: Ord a => (forall n. Term a n -> Maybe (Term a n)) -> Term a m -> Term a m
rewriteAll f = fixedpoint (rewrite f)

-------------------------------------------------------------------------------
-- Bindings
-------------------------------------------------------------------------------

-- | Term with arity.
--
-- The arity is not exact, but it is at least the given value.
type DefnWithArity :: Type -> Nat -> Type
data DefnWithArity a n = DefnWithArity !Int !(Defn a n)

-- | Definitions
type Definitions :: Type -> Nat -> Type
newtype Definitions a n = Definitions (Map (Var n) (DefnWithArity a n))

instance Rename (DefnWithArity a) where
    r <@> DefnWithArity a t = DefnWithArity a (r <@> t)

instance Rename (Definitions a) where
    r <@> Definitions ctx = Definitions $ Map.fromList . map (bimap (renameVar r) (r <@>)) . Map.toList $ ctx

definitionsEmpty :: Definitions m a
definitionsEmpty = Definitions Map.empty

definitionsOnLet :: Name -> Defn a m -> Definitions a m -> Definitions a ('S m)
definitionsOnLet _ t ctx =
    Definitions (Map.insert VZ (DefnWithArity a (weaken t)) ctx')
  where
    a = defnArity t
    Definitions ctx' = weaken ctx

-- | Variable definition arity is at least the returned value.
definitionArity :: Definitions a n -> Var n ->  Int
definitionArity ctx x = case definitionLookup ctx x of
    Just (DefnWithArity a _) -> a
    Nothing                  -> 0

definitionLookup  :: Definitions a n -> Var n -> Maybe (DefnWithArity a n)
definitionLookup (Definitions ctx) x = Map.lookup x ctx

isUnsaturatedApp :: Definitions a n -> Term a n -> Bool
isUnsaturatedApp ctx (Defn (Neutral (HeadVar f) args))
    | a <- definitionArity ctx f
    , length args < a
    = True
isUnsaturatedApp _ _ = False

rewriteWithDefinitions
    :: Ord a
    => (forall m. Definitions a m -> Term a m -> Maybe (Term a m))
    -> Term a n
    -> Term a n
rewriteWithDefinitions f = rewriteWith f definitionsOnLet definitionsEmpty

rewrite1WithDefinitions
    :: Ord a
    => (forall m. Definitions a m -> Term a m -> Maybe (Term a m))
    -> Term a n
    -> Term a n
rewrite1WithDefinitions f = rewrite1With f definitionsOnLet definitionsEmpty
