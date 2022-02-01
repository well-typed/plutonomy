{-# LANGUAGE DefaultSignatures #-}
-- |
-- Influenced by
--
-- * Edward Kmett's gist https://gist.github.com/ekmett/460ba28a3655c47e84c4135bc17b856f
--
-- * and Stephanie Weirich's challenge https://github.com/sweirich/challenge/blob/bdd86d4e25a4d139415fcdb77d8ad58f3fc44034/debruijn/src/SubstScoped.hs
--
module Subst (
    -- * Substitutions
    Sub,
    substVar,
    idSub,
    liftSub,
    -- * Things with variables
    Vars (..),
    closed,
    -- * Substitable things
    Subst (..),
    renameDefault,
    instantiate1,
    -- * Things with free variables
    Free (..),
    closedFree,
    vacuousFree,
    abstract1,
    -- * Variables
    module Subst.Var,
    Nat (..),
) where

import Data.Coerce           (coerce)
import Data.Functor.Identity (Identity (..))
import Data.Kind             (Type)
import Data.Type.Nat         (Nat (..))
import Data.Void             (Void, absurd)

import qualified Control.Category as C

import Subst.Var

-- | Substitution.
type Sub :: (Nat -> Type) -> Nat -> Nat -> Type
newtype Sub term n m = Sub
    { substVar :: Var n -> term m
      -- ^ Substitution action on variables.
    }

-- | Identity substitution.
idSub :: Vars term => Sub term n n
idSub = Sub var

-- | Lift substitution. Use this when you under a binder.
liftSub :: Subst term => Sub term n m -> Sub term (S n) (S m)
liftSub (Sub sub) = Sub $ \v -> case v of
    VZ   -> var VZ
    VS n -> weaken (sub n)

-------------------------------------------------------------------------------
-- Term
-------------------------------------------------------------------------------

-- | 
class Rename term => Vars term where
    -- | Lift variable to @term@.
    var   :: Var n -> term n

    -- | Variable traversal.
    bound  :: Applicative f => (Var n -> f (Var m)) -> term n -> f (term m)
    default bound :: (Applicative f, Free term', term ~ term' a) => (Var n -> f (Var m)) -> term n -> f (term m)
    bound = flip vars pure

-- | Terms supporting substition. You need to implement this for your term data type.
--
-- Note the similarity with 'Monad': 'var' is like 'return', 'subst' is like '>>='.
--
class Vars term => Subst term where
    -- | Subsitute.
    subst :: Sub term n m -> term n -> term m

-- | Rename term using 'Term' substitution.
renameDefault :: Subst term => Ren n m -> term n -> term m
renameDefault r = subst (Sub $ var . (r <@>))

instance Subst term => C.Category (Sub term) where
    id          = Sub var
    s1 . Sub s2 = Sub (subst s1 . s2)


-- | Instantiate the first variable with a term.
instantiate1 :: Subst term => term n -> term (S n) -> term n
instantiate1 t = subst $ Sub $ \x -> case x of
    VZ   -> t
    VS n -> var n

-- | Is term closed.
closed :: Subst term => term n -> Maybe (term Z)
closed t = bound (const Nothing) t

-------------------------------------------------------------------------------
-- Term with free variables
-------------------------------------------------------------------------------

-- | Terms with free variables.
class (forall a. Subst (term a)) => Free term where
    -- | Create term with a free var.
    ret :: a -> term a n

    -- | Substitute free variables. (Like '>>=')
    (>>==) :: term a n -> (a -> term b n) -> term b n

    -- | Free variable traversal.
    free :: Applicative f => (a -> f b) -> term a n -> f (term b n)
    free = vars pure

    -- | Traverse over free and bound variables.
    vars :: Applicative f => (Var n -> f (Var m)) -> (a -> f b) -> term a n -> f (term b m)

infixl 4 >>==

-- | Abstract over a free variable.
abstract1 :: (Eq a, Free term) => a -> term a n -> term a (S n)
abstract1 n t = weaken t >>== \x -> if x == n then var VZ else ret x

-- | Closed term can be weakened.
vacuousFree :: Free term => term Void Z -> term a n
vacuousFree = vars' (absurdRen <@>) absurd where
    vars' :: forall term n m a b. Free term => (Var n -> Var m) -> (a -> b) -> term a n -> term b m
    vars' = coerce (vars @term @Identity @n @m @a @b)

-- | Is term closed.
closedFree :: Free term => term a n -> Maybe (term Void Z)
closedFree = vars (const Nothing) (const Nothing)
