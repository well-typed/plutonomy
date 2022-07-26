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

data Wk n m where
    WkId   :: Wk n n
    WkLift :: Wk n m -> Wk (S n) (S m)
    WkSkip :: Wk n m -> Wk n (S m)

unliftWk' :: forall n m r. Wk (S n) m -> (forall p. S p ~ m => Wk n p -> r) -> r
unliftWk' WkId        k = k WkId
unliftWk' (WkLift wk) k = k wk
unliftWk' (WkSkip wk) k = unliftWk' wk $ \wk' -> k (WkSkip wk')

unliftWk :: Wk (S n) (S m) -> Wk n m
unliftWk wk = unliftWk' wk id

instance C.Category Wk where
    id = WkId

    WkId      . wk'        = wk'
    WkSkip wk . wk'        = WkSkip (wk C.. wk')
    WkLift wk . WkId       = WkLift wk
    WkLift wk . WkSkip wk' = WkSkip (wk C.. wk')
    WkLift wk . WkLift wk' = WkLift (wk C.. wk')

wkToRen :: Wk n m -> Ren n m
wkToRen WkId        = idRen
wkToRen (WkLift wk) = liftRen (wkToRen wk)
wkToRen (WkSkip wk) = skipRen (wkToRen wk)

-------------------------------------------------------------------------------
-- Lets state
-------------------------------------------------------------------------------

data Lets tag a n m p q where
    Lets :: Map tag (Var p)
         -> Add m p q
         -> Ren n p
         -> (Raw a p -> Raw a n)
         -> Lets tag a n m p q

data Add n (m :: Nat) (p :: Nat) where
    AZ :: Add Z m m
    AS :: Add n m p -> Add (S n) m (S p)

addL :: Add n m q -> (Add n (S m) (S q), Wk q (S q))
addL AZ     = (AZ, WkSkip WkId)
addL (AS a) = let (a', wk') = addL a in (AS a', WkLift wk')

addWk :: Add m p q -> Var p -> Var q
addWk AZ x = x
addWk (AS a) x = VS (addWk a x)

addRen :: Add m p q -> Ren p q
addRen AZ     = idRen
addRen (AS a) = skipRen (addRen a)

idLets :: Lets tag a n Z n n
idLets = Lets Map.empty AZ C.id id 

liftLets :: Lets tag a n m p q -> Lets tag a n (S m) p (S q)
liftLets (Lets xs add wk mk) = Lets xs (AS add) wk mk

applyLets :: Lets tag a n Z p q -> Raw a q -> Raw a n
applyLets (Lets _xs AZ _wk mk) t = mk t

-------------------------------------------------------------------------------
-- Traversal
-------------------------------------------------------------------------------

bindLet :: forall tag a n m p q r. Ord tag => Lets tag a n m p q -> tag -> Name -> Raw a n -> (forall p' q'. Wk q q' -> Lets tag a n m p' q' -> Raw a q' -> r) -> r
bindLet lets@(Lets xs add wk mk) tag name t kont = case Map.lookup tag xs of
    Just x  -> kont WkId   lets                                                                                      (Var (addWk add  x))
    Nothing -> kont wk'   (Lets (Map.insert tag x (Map.map weaken xs)) add' (skipRen wk) (mk . Let name (wk <@> t))) (Var (addWk add' x))
      where
        x :: Var (S p)
        x = VZ

        add' :: Add m (S p) (S q)
        wk'  :: Wk q (S q)

        (add', wk') = addL add

withLets 
    :: forall a b n tag. (forall r' m p q. Lets tag b n m p q -> a -> (forall p' q'. Wk q q' -> Lets tag b n m p' q' -> Raw b q' -> r') -> r')
    -> Raw a n -> Raw b n
withLets f t0 = go idLets t0 $ \ _wk -> applyLets
  where
    go :: forall m p q r. Lets tag b n m p q -> Raw a q -> (forall p' q'. Wk q q' -> Lets tag b n m p' q' -> Raw b q' -> r ) -> r
    go lets (Free x) k =
        f lets x k
    go lets (App t s) k =
        go lets  t                   $ \wk1 lets1 t' ->
        go lets1 (wkToRen wk1 <@> s) $ \wk2 lets2 s' ->
        k (wk1 C.>>> wk2) lets2 (App (wkToRen wk2 <@> t') s')
    go lets (Lam n t) k = 
        go (liftLets lets) t $ \wk1 (Lets xs (AS add) wk mk) t' ->
        k (unliftWk wk1) (Lets xs add wk mk) (Lam n t')
    go lets (Let n t s) k =
        go lets t $ \wk1 lets1 t' ->
        go (liftLets lets1) (wkToRen (WkLift wk1) <@> s) $ \wk2 (Lets xs (AS add) wk mk) s' ->
        k (wk1 C.>>> unliftWk wk2) (Lets xs add wk mk) (Let n (wkToRen (unliftWk wk2) <@> t') s')
    go lets (Delay t) k =
        go lets t $ \wk lets' t' -> k wk lets' (Delay t')
    go lets (Force t) k =
        go lets t $ \wk lets' t' -> k wk lets' (Force t')
    go lets (Constant c) k =
        k WkId lets (Constant c)
    go lets (Builtin b) k =
        k WkId lets (Builtin b)
    go lets Error k =
        k WkId lets Error
    go lets (Var x) k =
        k WkId lets (Var x)

substFreeWithLet
    :: Ord tag
    => (tag -> (Name, Raw b n))
    -> (a -> Either tag (Raw b n))
    -> Raw a n
    -> Raw b n
substFreeWithLet g f = withLets $ \lets@(Lets _ add ren _) a k ->
    case f a of
        Left tag -> bindLet lets tag n t k where
            (n, t) = g tag

        Right t  -> k WkId lets ((ren C.>>> addRen add) <@> t)
