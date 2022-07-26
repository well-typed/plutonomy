{-# LANGUAGE CPP #-}
-- | Variables for well-scoped terms.
module Subst.Var (
    -- * Variables
    Var (VZ,VS),
    absurdVar,
    unvar,
    pattern V0,
    pattern V1,
    pattern V2,
    -- ** Common patterns
    unusedVar,
    unusedVar2,
    unusedVar3,
    -- * Rens
    Ren,
    mkRen,
    renameVar,
    idRen,
    liftRen,
    skipRen,
    compRen,
    bumpRen,
    swapRen,
    weakenRen,
    absurdRen,
    -- * Rename things
    Rename (..),
    rename,
    bump,
    weaken,
    vacuous,
    NoCtx (..),
) where

import Data.Kind            (Type)
import Data.Nat             (Nat (..))

import qualified Control.Category as C

#ifdef SAFE
#else
import Unsafe.Coerce (unsafeCoerce)
#endif

-- | Variables index the context size.
type Var :: Nat -> Type
type role Var nominal

pattern V0 :: Var (S n)
pattern V0 = VZ

pattern V1 :: Var (S (S n))
pattern V1 = VS V0

pattern V2 :: Var (S (S (S n)))
pattern V2 = VS V1

#ifdef SAFE

data Var n where
    VZ :: Var (S n)
    VS :: Var n -> Var (S n)

indexVar :: Var n -> Int
indexVar = go 0 where
    go :: Int -> Var j -> Int
    go !acc VZ = acc
    go acc (VS n) = go (acc + 1) n

-- | Derive anything from variable in empty scope.
--
-- Note: don't use @EmptyCase@ as it doesn't work for unsafe representation.
absurdVar :: Var Z -> a
absurdVar x = case x of {}

#else

-- Vars which are just 'Int's.

newtype Var j = UnsafeVar { indexVar :: Int }

-- | Derive anything from variable in empty scope.
--
-- Note: don't use @EmptyCase@ as it doesn't work for unsafe representation.
absurdVar :: Var Z -> a
absurdVar x = x `seq` error "absurd: Var Z"

-- We need a GADT to implement pattern synonyms.
type Var' :: Nat -> Type
type role Var' nominal
data Var' n where
    VZ' :: Var' (S n)
    VS' :: Var n -> Var' (S n)

upVar :: Var n -> Var' n
upVar (UnsafeVar 0) = unsafeCoerce VZ'
upVar (UnsafeVar n) = unsafeCoerce (VS' (UnsafeVar (n - 1)))

pattern VZ :: () => (m ~ S n) => Var n
pattern VZ <- (upVar -> VZ') where
    VZ = UnsafeVar 0

pattern VS :: () => (m ~ S n) => Var n -> Var m
pattern VS n <- (upVar -> VS' n) where
    VS n = UnsafeVar (indexVar n + 1)

{-# COMPLETE VZ, VS #-}

#endif

-------------------------------------------------------------------------------
-- Common
-------------------------------------------------------------------------------

deriving instance Eq (Var n)
deriving instance Ord (Var n)

instance Show (Var j) where
    showsPrec d = showsPrec d . indexVar

-- | Case on 'Var'. (compare to 'maybe').
unvar :: a -> (Var n -> a) -> Var (S n) -> a
unvar z _ VZ     = z
unvar _ s (VS x) = s x

-- | Is variable unused?
unusedVar :: Var (S n) -> Maybe (Var n)
unusedVar (VS x) = Just x
unusedVar _      = Nothing

-- | Are two variables unused?
unusedVar2 :: Var (S (S n)) -> Maybe (Var n)
unusedVar2 (VS (VS x)) = Just x
unusedVar2 _           = Nothing

-- | Are three variables unused?
unusedVar3 :: Var (S (S (S n))) -> Maybe (Var n)
unusedVar3 (VS (VS (VS x))) = Just x
unusedVar3 _                = Nothing

-------------------------------------------------------------------------------
-- Rens
-------------------------------------------------------------------------------

-- | Rens are mappings of variable.
type Ren :: Nat -> Nat -> Type
newtype Ren n m = Ren
    { renameVar :: Var n -> Var m -- ^ Apply 'Ren' to a variable.
    }

-- | Identity renamings.
idRen :: Ren n n
idRen = Ren id

-- | Make a 'Ren' from a fuinction.
mkRen :: (Var n -> Var m) -> Ren n m
mkRen = Ren

-- | Lift renaming (used when going under a binder).
liftRen :: Ren n m -> Ren (S n) (S m)
liftRen (Ren f) = Ren (go f)
  where
    go :: (Var n -> Var m) -> Var (S n) -> Var (S m)
    go _ VZ     = VZ
    go g (VS x) = VS (g x)

skipRen :: Ren n m -> Ren n (S m)
skipRen (Ren f) = Ren (VS . f)

-- we need to bind tighter then <@>
infixr 9 `compRen`

-- | Ren composition.
compRen :: Ren a b -> Ren b c -> Ren a c
Ren r `compRen` Ren r' = Ren (r' . r)

instance C.Category Ren where
    id  = idRen
    (.) = flip compRen

-- | Weakening of a context.
weakenRen :: Ren n (S n)
weakenRen = skipRen idRen

-- | Common renaming weakening under one variable.
--
-- @
-- 'bump' = 'liftRen' 'weaken'
-- @
bumpRen :: Ren (S n) (S (S n))
bumpRen = liftRen weakenRen

-- | Swap two top variables in the context.
--
-- /Note:/ this is one case why we cannot use thinnings.
swapRen :: Ren (S (S n)) (S (S n))
swapRen = Ren swap' where
    swap' :: Var (S (S n)) -> Var (S (S n))
    swap' VZ      = VS VZ
    swap' (VS VZ) = VZ
    swap' v       = v

-- | Zero variables can be renamed to any number of variables.
absurdRen :: Ren Z m
absurdRen = Ren absurdVar

-------------------------------------------------------------------------------
-- Rename
-------------------------------------------------------------------------------

-- | Rename things.
class Rename t where
    (<@>) :: Ren n m -> t n -> t m

infixl 4 <@>

-- | Rename term: '<@>'.
rename :: Rename t => Ren n m -> t n -> t m
rename = (<@>)

bump :: Rename t => t (S n) -> t (S (S n))
bump = rename bumpRen

-- | Weaken term.
weaken :: Rename term => term n -> term (S n)
weaken = rename weakenRen

-- | Closed term can be weakened.
vacuous :: Rename term => term Z -> term n
vacuous = rename absurdRen

-- | No context.
--
-- Used to implement 'rewrite' in terms of 'rewriteWith' etc.
type NoCtx :: Nat -> Type
data NoCtx n = NoCtx

instance Rename NoCtx where
    _ <@> _ = NoCtx

instance Rename Var where
    r <@> x = renameVar r x

instance Rename (Ren n) where
    f <@> g = compRen g f
