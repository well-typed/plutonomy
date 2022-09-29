module Plutonomy.Raw.Lets (
    substFreeWithLet,
) where

import Plutonomy.Name
import Plutonomy.Raw
import Subst

import qualified Control.Category as C
import           Data.Map         (Map)
import qualified Data.Map.Strict  as Map

-------------------------------------------------------------------------------
-- Weakening
-------------------------------------------------------------------------------

-- Weakening
--
-- A variant where 'WkId' is a constructor.
--
data Wk n m where
    WkId   :: Wk n n
    WkLess :: Wk' n m -> Wk n m

data Wk' n m where
    Wk     ::            Wk' n     (S n)
    WkSkip :: Wk' n m -> Wk' n     (S m)
    WkKeep :: Wk' n m -> Wk' (S n) (S m)

wkKeep :: Wk n m -> Wk (S n) (S m)
wkKeep WkId        = WkId
wkKeep (WkLess wk) = WkLess (WkKeep wk)

-- Removes the first 'WkKeep'.
--
-- See a note for 'addL', the type for this function would
-- also be more complicated, as a value is actually removed from somewhere
-- in @q@ context. (But actually it's always on the top).
--
unliftWk :: Wk (S n) (S m) -> Wk n m
unliftWk wk = unliftWk' wk id

unliftWk' :: forall n m r. Wk (S n) m -> (forall p. S p ~ m => Wk n p -> r) -> r
unliftWk' WkId        k = k WkId
unliftWk' (WkLess wk) k = unliftWk'' wk $ \wk' -> k (WkLess wk')

unliftWk'' :: forall n m r. Wk' (S n) m -> (forall p. S p ~ m => Wk' n p -> r) -> r
unliftWk'' Wk k = k Wk
unliftWk'' (WkKeep wk) k = k wk
unliftWk'' (WkSkip wk) k = unliftWk'' wk $ \wk' -> k (WkSkip wk')

composeWk' :: Wk' a b -> Wk' b c -> Wk' a c
composeWk' wk          Wk           = WkSkip wk
composeWk' wk          (WkSkip wk') = WkSkip (composeWk' wk wk')
composeWk' Wk          (WkKeep wk') = WkSkip wk'
composeWk' (WkSkip wk) (WkKeep wk') = WkSkip (composeWk' wk wk')
composeWk' (WkKeep wk) (WkKeep wk') = WkKeep (composeWk' wk wk')

instance C.Category Wk where
    id = WkId

    WkId      . wk'        = wk'
    wk        . WkId       = wk
    WkLess wk . WkLess wk' = WkLess (composeWk' wk' wk)

-- Weakening can be converted to renaming.
wkToRen :: Wk n m -> Ren n m
wkToRen WkId        = idRen
wkToRen (WkLess wk) = wkToRen' wk

wkToRen' :: Wk' n m -> Ren n m
wkToRen' Wk          = skipRen idRen
wkToRen' (WkSkip wk) = skipRen (wkToRen' wk)
wkToRen' (WkKeep wk) = liftRen (wkToRen' wk)

-------------------------------------------------------------------------------
-- Lets state
-------------------------------------------------------------------------------

-- @Lets@ keeps the state of on-going let insertion.
--
-- * @tag@ is a key type for let-inserted bindings, so we insert them at most once.
--
-- * @a@ is a type of free variables.
--
-- The rest four @:: Nat@ indices describe the context structure
--
-- * @n@ is the initial context
-- * @p@ is the context with inserted let bindings
-- * @m@ is the binders ('Lam', 'Let', ...) we have gone under
-- * @q@ is the complete context.
--
-- Graphically
--
-- |.... n ....|       |          |
-- |............ p ....|.... m....|
-- |................. q ..........|
--
data Lets tag a n m p q where
    Lets :: Map tag (Var p)        -- ^ map from inserted bindings to their variable
         -> Add m p q              -- ^ an evidence that m + p = q
         -> Ren n p                -- ^ weakening from n to p (i.e. n is a subcontext of p)
         -> (Raw a p -> Raw a n)   -- ^ a term constructor from p to n, i.e. inserting the lets.
         -> Lets tag a n m p q

-- An evidence that @m + p = q@
--
-- Having an a graph of function allows us to pattern match on it.
-- That is useful.
data Add m (p :: Nat) (q :: Nat) where
    AZ :: Add Z p p
    AS :: Add m p q -> Add (S m) p (S q)

-- The need for this function would been clearer in well-typed representation.
-- There + is append ++, and S is snocing an element.
--
-- So here we go from:
--
-- |............ p ....|.... m....|
-- |................. q ..........|
--
-- to
--
-- |............ p ....|1|.... m....|
-- |................. S q ..........|
--
-- but because contexts are just sizes, the new context is S q
-- and not a @p ++ [a] ++ m@
--
-- In comparison, @AS@ constructor adds an element to the ends of @m@ and @q@.
--
-- * 'AS'   is used when we go under local binders
-- * 'addL' is used when we add new let-bindings
--
addL :: Add m p q -> (Add m (S p) (S q), Wk q (S q))
addL AZ     = (AZ, WkLess Wk)
addL (AS a) = let (a', wk') = addL a in (AS a', wkKeep wk')

-- | Using @Add m p q@ we can map @Var p@ to @Var q@
addWk :: Add m p q -> Var p -> Var q
addWk AZ x     = x
addWk (AS a) x = VS (addWk a x)

-- | See 'addWk': or have a 'Ren' (renaming).
addRen :: Add m p q -> Ren p q
addRen add = mkRen (addWk add)

-- | There is an empty 'Lets', with no binders went-under, nor let-bindings.
idLets :: Lets tag a n Z n n
idLets = Lets Map.empty AZ C.id id

-- | We can go under the binder, by increasing @m@ (and @q@).
liftLets :: Lets tag a n m p q -> Lets tag a n (S m) p (S q)
liftLets (Lets xs add wk mk) = Lets xs (AS add) wk mk

-- | If there is no binders in 'Lets', i,e. @m@ is zero,
-- we can convert term in current context to the term in the initial context.
applyLets :: Lets tag a n Z p q -> Raw a q -> Raw a n
applyLets (Lets _xs AZ _wk mk) t = mk t

-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

-- | The return type for 'bindLet', and inner function in 'withLets'.
--
data Ret tag a n m q where
    Ret :: Wk q q' -> Lets tag a n m p' q' -> Raw a q' -> Ret tag a n m q

-- 'bindLet' is the first complicated function.
--
-- Given a 'Lets', a tag, a name and a term,
-- We'll produce a new contexts p' (and q' = p' + m),
-- such that we can weaken from q to q' (i.e. q' is larger than q)
-- a new lets and a shared original term (This could been just a variable as well).
--
-- If Haskell had existential types, instead of continuation we could written:
--
-- @
-- ..
-- -> exists p' q. (Wk q q', Lets tag a n m p' q', Raw a q')
-- @
--
-- but we use a continuation to encode that.
--
-- Note, here @p'@ is either @p@ or @S p@,
-- we either insert a binding or we don't (if it's already inserted);
-- but later when we traverse syntax trees the context might grow arbitrarily.
--
bindLet
    :: forall tag a n m p q. Ord tag
    => Lets tag a n m p q -> tag -> Name -> Raw a n
    -> Ret tag a n m q
bindLet lets@(Lets xs add wk mk) tag name t = case Map.lookup tag xs of
    Just x  -> Ret WkId  lets                                                                                      (Var (addWk add  x))
    Nothing -> Ret wk'  (Lets (Map.insert tag x (Map.map weaken xs)) add' (skipRen wk) (mk . Let name (wk <@> t))) (Var (addWk add' x))
      where
        x :: Var (S p)
        x = VZ

        add' :: Add m (S p) (S q)
        wk'  :: Wk q (S q)

        (add', wk') = addL add

-- | 'withLet' is a traversal function for 'Raw' AST.
-- On each free variable occurence,
-- we essentially map to a 'Raw b' term,
-- but also can insert arbitrary let bindings on top level.
--
withLets
    :: forall a b n tag. (forall m p q. Lets tag b n m p q -> a -> Ret tag b n m q)
    -> Raw a n -> Raw b n
withLets f t0 = case go idLets t0 of
    Ret _wk lets t -> applyLets lets t
  where
    go :: forall m p q. Lets tag b n m p q -> Raw a q -> Ret tag b n m q
    go lets (Free x) =
        f lets x
    go lets (App t s) =
        case go lets  t                   of { Ret wk1 lets1 t' ->
        case go lets1 (wkToRen wk1 <@> s) of { Ret wk2 lets2 s' ->
        Ret (wk1 C.>>> wk2) lets2 (App (wkToRen wk2 <@> t') s') }}
    go lets (Lam n t) =
        case go (liftLets lets) t of { Ret wk1 (Lets xs (AS add) wk mk) t' ->
        Ret (unliftWk wk1) (Lets xs add wk mk) (Lam n t') }
    go lets (Let n t s) =
        case go lets             t                            of { Ret wk1 lets1 t' ->
        case go (liftLets lets1) (wkToRen (wkKeep wk1) <@> s) of { Ret wk2 (Lets xs (AS add) wk mk) s' ->
        Ret (wk1 C.>>> unliftWk wk2) (Lets xs add wk mk) (Let n (wkToRen (unliftWk wk2) <@> t') s') }}
    go lets (Delay t) =
        case go lets t of Ret wk lets' t' -> Ret wk lets' (Delay t')
    go lets (Force t) =
        case go lets t of Ret wk lets' t' -> Ret wk lets' (Force t')
    go lets (Constant c) =
        Ret WkId lets (Constant c)
    go lets (Builtin b) =
        Ret WkId lets (Builtin b)
    go lets Error =
        Ret WkId lets Error
    go lets (Var x) =
        Ret WkId lets (Var x)

-- |  The 'substFreeWithLet' is a generalization of @substFree@
-- but instead of having @(a -> Raw b n)@ substitution,
-- we can opt to refer to a just-inserted bindings.
--
substFreeWithLet
    :: Ord tag
    => (tag -> (Name, Raw b n))      -- ^ a term (and its name) for a tag
    -> (a -> Either tag (Raw b n))   -- ^ substitution to either a new term, or let-inserted binding.
    -> Raw a n                       -- ^ initial term
    -> Raw b n                       -- ^ term with free variables substituted
substFreeWithLet g f = withLets $ \lets@(Lets _ add ren _) a ->
    case f a of
        Left tag -> bindLet lets tag n t where
            (n, t) = g tag

        Right t  -> Ret WkId lets ((ren C.>>> addRen add) <@> t)

-- The implementation of 'substFreeWithLet' combines 'withLets' with 'bindLet'.
