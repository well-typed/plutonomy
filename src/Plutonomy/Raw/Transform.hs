{-# LANGUAGE OverloadedStrings #-}
module Plutonomy.Raw.Transform (
    -- * Transformations
    simplify,
    commonBindings,
    splitDelay,
    splitDelay',
    inlineSaturated,
    inlineSaturated',
    prelude,
    floatIn,
    floatIn',
    renameLets,
    -- commonTraces,
    cse,
    -- * Rewrites of known terms
    knownRewrites,
    IfeRewrite (..),
    TraceRewrite (..),
    -- * Single rewrites
    letFromLet,
    forceDelay,
    unusedBinding,
    inlineUsedOnce,
    inlineUsedOnce',
    appError, AppError (..),
    etaForce,
    etaFun,
    floatOutLambda,
    floatOutDelay,
    floatOutAppArg, FloatOutAppArg (..),
    ifLambda,
    commEquals,
    letZero,
    inlineConstants,
    -- * Helpers
    inlineSize,
    -- * Inconsistent
    forcedBuiltin,
) where

import Control.Applicative (Const (..))
import Control.Category    ((>>>))
import Data.Bifunctor      (bimap)
import Data.Char           (isAlphaNum)
import Data.List           (sortOn)
import Data.Map.Strict     (Map)
import Data.Maybe          (fromMaybe)
import Data.Monoid         (Sum (..))
import Data.Ord            (Down (..))
import Data.Void           (Void, absurd)
import PlutusCore.Default  (DefaultFun (..))
import Subst
       (Free (..), Nat (S, Z), Rename (..), Var (..), Vars (..), bump, closed, closedFree, compRen, instantiate1, mkRen, rename, unusedVar,
       unusedVar2, unusedVar3, unvar, vacuousFree, weaken, weakenRen)

import qualified Control.Lens    as L
import qualified Data.Map.Strict as Map
import qualified Data.Text       as T
import qualified Prettyprinter   as PP

import Plutonomy.Constant
import Plutonomy.Conversion
import Plutonomy.Known
import Plutonomy.MissingH
import Plutonomy.Name
import Plutonomy.PlutusExtras
import Plutonomy.Pretty
import Plutonomy.Raw
import Plutonomy.Raw.Rewrite

import qualified UntypedPlutusCore as UPLC

-- $setup
-- >>> import Plutonomy
-- >>> import Plutonomy.Raw.Rewrite
-- >>> import Plutonomy.Known
-- >>> import Plutonomy.MissingH
-- >>> import Subst
-- >>> import Data.Text (Text)
-- >>> import Control.Monad (forM_)
-- >>> import PlutusCore.Default (DefaultFun (..))
-- >>> import qualified Prettyprinter as PP
-- >>> let pp t = prettyRaw PP.pretty (t :: Raw Text Z)

-------------------------------------------------------------------------------
-- prelude
-------------------------------------------------------------------------------

-- | Prelude ads bindings with familiar names.
-- This makes dumps more uniform.
--
-- >>> pp $ prelude "..."
-- let* id = \ x -> x
--      ~id = \ ~ y -> y
--      ~~id = \ ~ ~ z -> z
--      const = \ u v -> u
--      flipConst = \ vv uu -> uu
--      True = \ ~ case_True case_False -> case_True
--      False = \ ~ case_True_ case_False_ -> case_False_
--      Just = \ justArg ~ case_Just case_Nothing -> case_Just justArg
--      Tuple2 = \ fst snd ~ case_Tuple2 -> case_Tuple2 fst snd
--      fstOf3 = \ m1 n1 p1 -> m1
--      sndOf3 = \ m2 n2 p2 -> n2
--      trdOf3 = \ m3 n3 p3 -> p3
--      EQ = \ ~ m4 n4 p4 -> m4
--      GT = \ ~ m5 n5 p5 -> n5
--      LT = \ ~ m6 n6 p6 -> p6
--      ~EQ = \ ~ ~ m7 n7 p7 -> m7
--      ~GT = \ ~ ~ m8 n8 p8 -> n8
--      ~LT = \ ~ ~ m9 n9 p9 -> p9
-- in ...
--
-- Note: @False@ and @Nothing@ are the same.
--
prelude :: Raw a n -> Raw a n
prelude t
    = Let "id"        (RawId "x")
    $ Let "~id"       (RawDelayId "y")
    $ Let "~~id"      (Delay (Delay (Lam "z" (Var VZ))))
    $ Let "const"     (RawConst "u" "v")
    $ Let "flipConst" (RawFlipConst "vv" "uu")
    $ Let "True"      (RawTrue "case_True" "case_False")
    $ Let "False"     (RawFalse "case_True_" "case_False_")
    $ Let "Just"      (Lam "justArg" $ Delay $ Lam "case_Just" $ Lam "case_Nothing" $ Var (VS VZ) :@ Var (VS (VS VZ)))
    $ Let "Tuple2"    (Lam "fst" $ Lam "snd" $ Delay $ Lam "case_Tuple2" $ Var VZ :@ Var (VS (VS VZ)) :@ Var (VS VZ))
    $ Let "fstOf3"    (RawFstOf3  "m1" "n1" "p1")
    $ Let "sndOf3"    (RawSndOf3  "m2" "n2" "p2")
    $ Let "trdOf3"    (RawTrdOf3  "m3" "n3" "p3")
    $ Let "EQ"        (RawEQ      "m4" "n4" "p4")
    $ Let "GT"        (RawGT      "m5" "n5" "p5")
    $ Let "LT"        (RawLT      "m6" "n6" "p6")
    $ Let "~EQ"       (RawDelayEQ "m7" "n7" "p7")
    $ Let "~GT"       (RawDelayGT "m8" "n8" "p8")
    $ Let "~LT"       (RawDelayLT "m9" "n9" "p9")
    $ rename (w % w % w % w % w % w % w % w % w % w % w % w % w % w % w % w % w % w) t
  where
    w   = weakenRen
    (%) = compRen
    infixr 9 %

-------------------------------------------------------------------------------
-- Simplify
-------------------------------------------------------------------------------

-- | Cheap reductions.
--
-- This function walks through whole syntax tree,
-- making local reduction on its way up.
--
-- === Lambda application
--
-- >>> let term = (lam_ "name" "body") :@ delay_ "def"
-- >>> pp term
-- (\ name -> body) (\ ~ -> def)
--
-- >>> pp $ simplify term
-- let* name = \ ~ -> def
-- in body
--
-- Nested:
--
-- >>> let term = (lam_ "name1" $ lam_ "name2" "body") :@ delay_ "def1" :@ delay_ "def2"
-- >>> term
-- App (App (Lam "name1" (Lam "name2" (Free "body"))) (Delay (Free "def1"))) (Delay (Free "def2"))
--
-- >>> pp term
-- (\ name1 name2 -> body) (\ ~ -> def1) (\ ~ -> def2)
--
-- >>> pp $ simplify term
-- let* name1 = \ ~ -> def1
--      name2 = \ ~ -> def2
-- in body
--
-- === Let floating
--
-- >>> let term = let_ "n" (delay_ "def") "f" :@ "x"
-- >>> pp term
-- (let* n = \ ~ -> def in f) x
--
-- >>> pp $ simplify term
-- let* n = \ ~ -> def
-- in f x
--
-- >>> let term = force_ (let_ "n" (delay_ "def") "x")
-- >>> pp term
-- (let* n = \ ~ -> def in x) !
--
-- >>> pp $ simplify term
-- let* n = \ ~ -> def
-- in x !
--
-- === Let-from-let
--
-- >>> let term = let_ "x" (let_ "y" (delay_ "foo") (delay_ "bar")) ("body" :@ "x" :@ "z")
-- >>> pp term
-- let* x = let* y = \ ~ -> foo in \ ~ -> bar
-- in body x z
--
-- >>> pp $ simplify term
-- let* y = \ ~ -> foo
--      x = \ ~ -> bar
-- in body x z
--
-- === Force delay
--
-- >>> let term = force_ (delay_ "t")
-- >>> pp term
-- (\ ~ -> t) !
--
-- >>> pp $ simplify term
-- t
--
simplify :: Raw a n -> Raw a n
-- simplify = H.toRaw . H.fromRaw
simplify = go where
    -- variables, builtins, constants and errors cannot be reduced.
    go :: Raw a n -> Raw a n
    go x@Var {}      = x
    go x@Free {}     = x
    go x@Builtin {}  = x
    go x@Constant {} = x
    go x@Error       = x

    go (App x y)   = app' (go x) (go y)
    go (Force t)   = force' (go t)
    go (Delay t)   = delay' (go t)
    go (Let n t s) = let' n (go t) (go s)
    go (Lam n t)   = lam' n (go t)

    app' :: Raw a n -> Raw a n -> Raw a n
    app' Error       _           = Error
    app' (Lam n t)   s           = let' n s t
    app' (Let n t r) s           = let' n t (app' r (weaken s))
    app' f           x           = App f x

    force' :: Raw a n -> Raw a n
    force' Error       = Error
    force' (Delay t)   = t
    force' (Let n t s) = let' n t (force' s)
    force' t           = Force t

    -- we don't instantiate constants, as these are big.
    let' :: Name -> Raw a n -> Raw a (S n) -> Raw a n
    let' _n t@(Var _)       s        = instantiate1 t s
    let' _n t@(Builtin _)   s        = instantiate1 t s
    let' _n t@(Free _)      s        = instantiate1 t s
    let' _n t@(Delay Error) s        = instantiate1 t s
    let' _n t@(Lam _ Error) s        = instantiate1 t s
    let' _n t@(Lam _ Var0)  s        = instantiate1 t s

    let' _n Error           _        = Error
    let' _n t               Var0     = t
    let'  x (Let y foo bar) body     = let' y foo $ let' x bar (bump body)
    let'  n t               s        = Let n t s

    lam' :: Name -> Raw a (S n) -> Raw a n
    lam' n t = Lam n t

    delay' :: Raw a n -> Raw a n
    delay' t = Delay t

-------------------------------------------------------------------------------
-- Renames
-------------------------------------------------------------------------------

-- | Rename let bindings
--
-- >>> let term = let_ "x" (lam_ "y" "y") $ let_ "x" (lams_ ["x","y"] "x") "foo"
-- >>> pp term
-- let* x = \ y -> y
--      x_0 = \ x_1 y_0 -> x_1
-- in foo
--
-- >>> pp $ renameLets term
-- let* id = \ y -> y
--      const = \ x y_0 -> x
-- in foo
--
renameLets :: forall n a . Ord a => Raw a n -> Raw a n
renameLets = rewrite1With onTerm onLet bindingsEmpty where
    onTerm :: Bindings a m -> Raw a m -> Maybe (Raw a m)
    onTerm  ctx (Let (Name n) t s)
        | T.length n < 2 -- rename one letter names only!
        , Just (Name n') <- nameTerm ctx t
        , T.length n' < 30 -- and new name is not super long!
        = Just (Let (Name n') t s)
    onTerm _ctx _term       = Nothing

    onLet :: Name -> Raw a m -> Bindings a m -> Bindings a ('S m)
    onLet n t ctx = bindingsOnLet (fromMaybe n (nameTerm ctx t)) t ctx

-------------------------------------------------------------------------------
-- CSE: Common bindings
-------------------------------------------------------------------------------

-- | Combine common bindings.
--
-- >>> let term = let_ "x" "foo" $ let_ "y" "foo" $ "f" :@ "x" :@ "y"
-- >>> pp term
-- let* x = foo
--      y = foo
-- in f x y
--
-- >>> pp $ commonBindings term
-- let* x = foo
-- in f x x
--
-- This is done only if we are binding a value.
--
commonBindings :: forall n a. Ord a => Raw a n -> Raw a n
commonBindings = rewriteWith f onLet (TermToVar Map.empty) where
    onLet :: Name -> Raw a m -> TermToVar a m -> TermToVar a (S m)
    onLet _ t (weaken -> TermToVar ctx)
        | isValue (const 0) t
        = TermToVar $ Map.insert (weaken t) VZ ctx

        | otherwise
        = TermToVar ctx

    f :: TermToVar a m -> Raw a m -> Maybe (Raw a m)
    f (TermToVar ctx) (Let _n t s)
        | isValue (const 0) t
        , Just x <- Map.lookup t ctx
        = Just (instantiate1 (Var x) s)

    f _ _ = Nothing

newtype TermToVar a n = TermToVar (Map (Raw a n) (Var n))

instance Ord a => Rename (TermToVar a) where
    r <@> TermToVar m = TermToVar $ Map.fromList . map (bimap (rename r) (rename r)) . Map.toList $ m

-------------------------------------------------------------------------------
-- CSE: Traces
-------------------------------------------------------------------------------

{-
commonTraces :: Ord a => Raw a n -> Raw a n
commonTraces term =
    go (rewrite rew (fmap Right term))
  where
    rew :: Term n (Either Text a) -> Maybe (Term n (Either Text a))
    rew (TraceError msg) = Just (Free (Left msg))
    rew _                = Nothing

    go :: Term n (Either Text a) -> Raw a n
    go t = case sequenceA t of
        Right t' -> t'
        Left msg -> go $
            Let (Name ("fail_" <> T.takeWhile isAlphaNum msg)) (TraceError msg) $
            weakenTerm t >>= \free -> case free of
                Left msg' | msg == msg' -> Var0
                x                       -> Free x

pattern TraceError ::  Text -> Raw a n
pattern TraceError t = Delay (Force (Force (Builtin Trace) :@ Constant (Some (ValueOf DefaultUniString t)) :@ Delay Error))
-}

-------------------------------------------------------------------------------
-- CSE: Common subexpression elimination
-------------------------------------------------------------------------------

-- | Common subexpression elimination.
--
-- >>> let term = "foo" :@ lams_ ["x","y","z"] "x" :@ lams_ ["u","v","w"] "u"
-- >>> pp term
-- foo (\ x y z -> x) (\ u v w -> u)
--
-- >>> pp $ cse 3 term
-- let* fstOf3 = \ u v w -> u
-- in foo fstOf3 fstOf3
--
--  Also forced terms can be cse'd:
--
-- >>> let term = "foo" :@ force_ (force_ trace_ :@ str_ "err" :@ tt_) :@ force_ (force_ trace_ :@ str_ "err" :@ tt_)
-- >>> pp term
-- foo (trace# ! "err"#t ()# !) (trace# ! "err"#t ()# !)
--
-- >>> pp $ cse 3 term
-- let* trace!_err_tt! = \ ~ -> trace# ! "err"#t ()# !
-- in foo (trace!_err_tt! !) (trace!_err_tt! !)
--
cse :: forall a n. Ord a => Integer -> Raw a n -> Raw a n
cse size = iterateWhileJust (cse' size)

cse' :: forall a n. Ord a => Integer -> Raw a n -> Maybe (Raw a n)
cse' size term = case terms of
      [] -> Nothing
      t : _
          | isValue (const 0) t -> Just $ Let
              (fromMaybe "cse" $ nameTerm bindingsEmpty t)
              (vacuousFree t)
              $ rewrite (rewExact t) (weaken (L.over free Just term)) >>== maybe Var0 Free

          | otherwise -> Just $ Let
              (fromMaybe "cse" (nameTerm bindingsEmpty t))
              (Delay (vacuousFree t))
              $ rewrite (rewForced t) (weaken (L.over free Just term)) >>== maybe Var0 Free
  where
    termsMap :: Map (Raw Void Z) Integer
    termsMap = Map.fromListWith (+) $ runDList $ foldTerm isClosed term

    -- terms occuring more then once, sorted by their termSize, starting from largest.
    terms :: [Raw Void Z]
    terms = sortOn (Down . termSize')
        [ t
        | (t, n) <- Map.toList termsMap
        , n > 1
        ]

    _trace :: String
    _trace = unlines
        [ show (termSize' t) ++ ": " ++ show (prettyRaw absurd t)
        | t <- terms
        ]

    rewExact :: Raw Void Z -> Raw (Maybe a) m -> Maybe (Raw (Maybe a) m)
    rewExact t t'
        | vacuousFree t == t' = Just (Free Nothing)
        | otherwise           = Nothing

    rewForced :: Raw Void Z -> Raw (Maybe a) m -> Maybe (Raw (Maybe a) m)
    rewForced t t'
        | vacuousFree t == t' = Just (Force (Free Nothing))
        | otherwise           = Nothing

    isClosed :: Raw a m -> DList (Raw Void Z, Integer)
    isClosed t
        | Just t' <- closedFree t
        , termSize t' >= size
        = dlistSingleton (t', 1)

        | otherwise
        = mempty

    termSize :: Raw Void Z -> Integer
    termSize = fst . termSize'

    termSize' :: Raw Void Z -> (Integer, Integer)
    termSize' t
        = (\t' -> (UPLC.serialisedSize t', UPLC.termSize t'))
        $ renameUPLC (\(UPLC.NamedDeBruijn _ i) -> UPLC.DeBruijn i)
        $ toUPLC t

nameTerm :: Bindings a n -> Raw a n -> Maybe Name
nameTerm _ t
    | Just k <- isKnown t
    = Just (knownName k)
nameTerm ctx (Var x)
    | Just (TermWithArity n _ _) <- lookupBinding ctx x
    = Just n
nameTerm _ (Builtin b)
    = Just $ Name $ T.pack $ show $ PP.pretty b
nameTerm ctx (Delay t)
    | Just (Name n) <- nameTerm ctx t
    = Just (Name (T.cons '~' n))
nameTerm _ (Constant (MkConstant IsText t))
    = Just $ Name $ T.take 15 $ T.map rep t
  where
    rep c = if isAlphaNum c then c else '_'
nameTerm _ (Constant (MkConstant IsUnit ()))
    = Just "unit"
nameTerm _ (Constant k)
    = Just $ Name $ T.pack $ take 15 $ map rep $ show $ PP.pretty k
  where
    rep c = if isAlphaNum c then c else '_'
nameTerm ctx (App f t)
    | Just (Name fn) <- nameTerm ctx f
    , Just (Name tn) <- nameTerm ctx t
    = Just (Name (fn <> "_" <> tn))
nameTerm ctx (Force t)
    | Just (Name n) <- nameTerm ctx t
    = Just (Name (T.snoc n '!'))
nameTerm _ _
    = Nothing



newtype DList a = DList ([a] -> [a])

instance Semigroup (DList a) where
    DList x <> DList y = DList (x . y)

instance Monoid (DList a) where
    mempty = DList id

runDList :: DList a -> [a]
runDList (DList x) = x []

dlistSingleton :: a -> DList a
dlistSingleton x = DList (x :)

-------------------------------------------------------------------------------
-- Inline delayed bindings
-------------------------------------------------------------------------------

-- | Split delayed binding definitions.
--
-- >>> let term = let_ "fix" (delay_ (delay_ (lam_ "x" ("x" :@ "x" :@ "x")))) (force_ (force_ "fix") :@ "f")
-- >>> pp term
-- let* fix = \ ~ ~ x -> x x x
-- in fix ! ! f
--
-- >>> pp $ splitDelay' term
-- let* fix = \ x -> x x x
--      fix_0 = \ ~ -> fix
--      fix_1 = \ ~ -> fix_0
-- in fix_1 ! ! f
--
-- Unused bindings will be removed by other passes.
--
-- >>> pp $ fixedpoint (simplify . inlineSaturated' 0) $ splitDelay' term
-- let* fix = \ x -> x x x
--      fix_0 = \ ~ -> fix
--      fix_1 = \ ~ -> fix_0
-- in fix f
--
-- If the just bound delayed term is forced immediately,
-- we can float it too
--
-- >>> let term = let_ "res" (delay_ $ "f" :@ "arg1" :@ "arg2") $ let_ "foo" ("g" :@ "bar" :@ force_ "res") "body"
-- >>> pp term
-- let* res = \ ~ -> f arg1 arg2
--      foo = g bar (res !)
-- in body
--
-- >>> pp $ splitDelay' term
-- let* res = f arg1 arg2
--      res_0 = \ ~ -> res
--      foo = g bar (res_0 !)
-- in body
--
-- >>> pp $ fixedpoint (simplify . inlineSaturated' 0) $ splitDelay' term
-- let* res = f arg1 arg2
--      res_0 = \ ~ -> res
--      foo = g bar res
-- in body
--
-- Unsaturated application:
--
-- >>> let term = let_ "f" (lams_ ["x","y","z"] $ "x" :@ "y" :@ "z") $ let_ "res" (delay_ $ "f" :@ "arg1" :@ "arg2") "body"
-- >>> pp term
-- let* f = \ x y z -> x y z
--      res = \ ~ -> f arg1 arg2
-- in body
--
-- >>> pp $ splitDelay' term
-- let* f = \ x y z -> x y z
--      res = f arg1 arg2
--      res_0 = \ ~ -> res
-- in body
--
splitDelay :: Bindings a n -> Raw a n -> Maybe (Raw a n)
splitDelay _ctx (Let _n (Delay (Var _)) _s) = Nothing
splitDelay  ctx (Let  n (Delay t)        s)
    | isValue (bindingArity ctx) t || VZ `isForcedIn` s
    = Just $ Let n t $ Let n (Delay (Var VZ)) $ bump s

splitDelay _ _ = Nothing

-- | Rewrite using 'splitDelay'.
splitDelay' :: Ord a => Raw a n -> Raw a n
splitDelay' = rewriteWithBindings splitDelay

isForcedIn :: Var n -> Raw a n -> Bool
isForcedIn x (Force (Var y)) = x == y
isForcedIn x (Force t)       = isForcedIn x t
isForcedIn x (App f t)       = isForcedIn x f || isForcedIn x t
isForcedIn x (Let _n t s)    = isForcedIn x t || isForcedIn (VS x) s

-- Lambda and Delay don't force
isForcedIn _ Lam {}   = False
isForcedIn _ Delay {} = False

isForcedIn _ Free {}     = False
isForcedIn _ Var {}      = False
isForcedIn _ Builtin {}  = False
isForcedIn _ Constant {} = False
isForcedIn _ Error {}    = False

isStrictIn :: Var n -> Raw a n -> Bool
isStrictIn x (Var y)         = x == y

isStrictIn x (Force t)       = isStrictIn x t
isStrictIn x (App f t)       = isStrictIn x f || isStrictIn x t
isStrictIn x (Let _n t s)    = isStrictIn x t || isStrictIn (VS x) s

-- Lambda and Delay don't force
isStrictIn _ Lam {}   = False
isStrictIn _ Delay {} = False

isStrictIn _ Free {}     = False
isStrictIn _ Builtin {}  = False
isStrictIn _ Constant {} = False
isStrictIn _ Error {}    = False

-------------------------------------------------------------------------------
-- Float In
-------------------------------------------------------------------------------

-- |
--
-- >>> let term = let_ "x" (delay_ ("f" :@ "arg")) $ "g" :@ (lam_ "y" $ "h" :@ force_ "x")
-- >>> pp term
-- let* x = \ ~ -> f arg
-- in g (\ y -> h (x !))
--
-- >>> pp $ floatIn' term
-- g (\ y -> h ((let* x = \ ~ -> f arg in x) !))
--
-- >>> let term = let_ "x" (delay_ ("f" :@ "arg")) $ "g" :@ (lam_ "y" $ "h" :@ force_ "x" :@ force_ "x")
-- >>> pp term
-- let* x = \ ~ -> f arg
-- in g (\ y -> h (x !) (x !))
--
-- >>> pp $ floatIn' term
-- g (\ y -> let* x = \ ~ -> f arg in h (x !) (x !))
--
-- >>> let term = let_ "x" (delay_ ("f1" :@ "arg1")) $ let_ "y" (delay_ ("f2" :@ "arg2")) $ "g" :@ (lam_ "z" $ "h" :@ force_ "x" :@ force_ "y" :@ "z")
-- >>> pp term
-- let* x = \ ~ -> f1 arg1
--      y = \ ~ -> f2 arg2
-- in g (\ z -> h (x !) (y !) z)
--
-- >>> pp $ floatIn' term
-- g
--   (\ z ->
--      h ((let* x = \ ~ -> f1 arg1 in x) !) ((let* y = \ ~ -> f2 arg2 in y) !) z)
--
-- Unsaturated example
--
-- >>> let term = let_ "f" (lams_ ["x","y","z"] $ "x" :@ "y" :@ "z") $ let_ "res" ("f" :@ "arg1" :@ "arg2") $ lams_ ["u","v"] "res"
-- >>> pp term
-- let* f = \ x y z -> x y z
--      res = f arg1 arg2
-- in \ u v -> res
--
-- >>> pp $ floatIn' term
-- \ u v -> let* res = (let* f = \ x y z -> x y z in f) arg1 arg2 in res
--
-- >>> pp $ fixedpoint (simplify . inlineUsedOnce') $ floatIn' term
-- \ u v z -> arg1 arg2 z
--
floatIn :: Bindings a n -> Raw a n -> Maybe (Raw a n)
floatIn ctx (Let n t0 s0)
    | isValue (bindingArity ctx) t0
    = go unusedVar t0 s0
  where
    push :: (Var m -> Maybe (Var n)) -> Var (S m) -> Maybe (Var (S n))
    push x = unvar (Just VZ) (fmap VS . x)

    go :: (Var m -> Maybe (Var n)) -> Raw a n -> Raw a m -> Maybe (Raw a n)
    go x d (App f t)
        | Just f' <- bound x f
        = App f' <$> go' x d t

        | Just t' <- bound x t
        = (\f' -> App f' t') <$> go' x d f

    go x d (Lam n' t)
        = Lam n' <$> go' (push x) (weaken d) t

    go x d (Let n' t s)
        | Just t' <- bound x t
        = Let n' t' <$> go' (push x) (weaken d) s

        | Just s' <- bound (unvar (Just VZ) (fmap VS . x)) s
        = (\t' -> Let n' t' s') <$> go' x d t

    go x d (Delay t)
        = Delay <$> go' x d t

    go x d (Force t)
        = Force <$> go x d t

    go _ _ _ = Nothing

    go' :: (Var m -> Maybe (Var n)) -> Raw a n -> Raw a m -> Maybe (Raw a n)
    go' x d term@(App f t)
        | Just f' <- bound x f
        = App f' <$> go' x d t

        | Just t' <- bound x t

        = (\f' -> App f' t') <$> go' x d f

        | otherwise
        = Just (Let n d (rename (mkRen $ maybe VZ VS . x) term))

    go' x d (Lam n' t)
        = Lam n' <$> go' (unvar (Just VZ) (fmap VS . x)) (weaken d) t

    go' x d (Delay t)
        = Delay <$> go' x d t

    go' x d (Force t)
        = Force <$> go' x d t

    go' x d term@(Let n' t s)
        | Just t' <- bound x t
        = Let n' t' <$> go' (unvar (Just VZ) (fmap VS . x)) (weaken d) s

        | Just s' <- bound (unvar (Just VZ) (fmap VS . x)) s
        = (\t' -> Let n' t' s') <$> go' x d t

        | otherwise
        = Just (Let n d (rename (mkRen $ maybe VZ VS . x) term))

    go' x d term
        = Just (Let n d (rename (mkRen $ maybe VZ VS . x) term))

floatIn _ _ = Nothing

-- | Rewrite using 'floatIn'.
floatIn' :: Ord a => Raw a n -> Raw a n
floatIn' = rewrite1WithBindings floatIn

-------------------------------------------------------------------------------
-- Inline linear bindings
-------------------------------------------------------------------------------

-- | Inline linear saturated bindings.
--
-- >>> let term = let_ "const" (lams_ ["x","y"] "x") ("const" :@ "foo" :@ "bar")
-- >>> pp term
-- let* const = \ x y -> x
-- in const foo bar
--
-- >>> pp $ inlineSaturated' 0 term
-- let* const = \ x y -> x
-- in (\ x_0 y_0 -> x_0) foo bar
--
-- >>> pp $ simplify $ inlineSaturated' 0 term
-- let* const = \ x y -> x
-- in foo
--
-- >>> pp $ inlineUsedOnce' $ simplify $ inlineSaturated' 0 term
-- foo
--
-- An example with @ERROR@:
--
-- >>> let term = let_ "const" (lam_ "x" $ lam_ "y" "x") ("const" :@ "foo" :@ Error)
-- >>> pp $ inlineSaturated' 0 term
-- let* const = \ x y -> x
-- in (\ x_0 y_0 -> x_0) foo ERROR
--
-- >>> pp $ inlineUsedOnce' $ simplify $ inlineSaturated' 0 term
-- ERROR
--
-- >>> let term = let_ "fail" (lam_ "ds" Error) $ "fail" :@ delay_ Error
-- >>> pp term
-- let* fail = \ ds -> ERROR
-- in fail (\ ~ -> ERROR)
--
-- >>> pp $ inlineSaturated' 0 term
-- let* fail = \ ds -> ERROR
-- in (\ ds_0 -> ERROR) (\ ~ -> ERROR)
--
-- >>> pp $ simplify $ inlineSaturated' 0 term
-- ERROR
--
inlineSaturated' :: Ord a => Integer -> Raw a n -> Raw a n
inlineSaturated' size = rewriteWithBindings (inlineSaturated size) where

inlineSaturated :: Ord a => Integer -> Bindings a m -> Raw a m -> Maybe (Raw a m)
inlineSaturated size ctx t@App{}
    | (Var f, args) <- peelApp t
    , Just (TermWithArity _n a f') <- lookupBinding ctx f
    , 0 < a, a <= length args
    , inlineSize f' >= size
    = Just (appArgs_ f' args)

inlineSaturated size ctx t@Force{}
    | (Var f, args) <- peelApp t
    , Just (TermWithArity _n a f') <- lookupBinding ctx f
    , 0 < a, a <= length args
    , inlineSize f' >= size
    = Just (appArgs_ f' args)

inlineSaturated _ _ _ = Nothing

-- | Inline size. Non-Negative means we want to inline this.
--
-- >>> inlineSize $ lam_ "x" "x"
-- 2
--
-- >>> inlineSize $ lams_ ["x","y"] "x"
-- 4
--
-- >>> inlineSize $ lams_ ["f","x"] $ "f" :@ "x"
-- 2
--
-- >>> inlineSize $ lams_ ["x","y","z"] $ "fun" :@ "x" :@ "y" :@ "z"
-- 0
--
-- >>> inlineSize $ lams_ ["f","x"] $ "f" :@ lams_ ["i","j","k","l"] "i"
-- -2
--
-- >>> inlineSize $ lams_ ["f","x"] $ "f" :@ "x" :@ "x"
-- 0
--
-- >>> inlineSize $ lams_ ["f","x"] $ "f" :@ lams_ ["i"] "i"
-- 1
--
-- >>> inlineSize $ lam_ "unused" Error
-- 3
--
-- Special cases:
--
-- >>> inlineSize $ delay_ $ force_ trace_ :@ lam_ "x" "x" :@ lam_ "y" "y"
-- -2
--
inlineSize :: Raw a n -> Integer
inlineSize (Delay term)
    | Just _ <- closed term
    , (Builtin Trace, _) <- peelApp term
    = -2
inlineSize term = top 1 term where
    top :: Integer -> Raw a n -> Integer
    top !acc (Lam _n t)   = top (2 + acc) t
    top !acc (Delay t)    = top (1 + acc) t
    top !acc t            = go acc t

    go :: Integer -> Raw a n -> Integer
    go  acc (Lam _n t)   = go (acc - 1) t
    go  acc (Var _)      = acc - 1
    go  acc (App f t)    = go (go (acc - 1) f) t
    go  acc (Delay t)    = go (acc - 1) t
    go  acc (Force t)    = go (acc - 1) t
    go  acc (Let _n t s) = go (go (acc - 1) t) s

    go  acc Error        = acc
    go  acc Free {}      = acc - 1
    go  acc Builtin {}   = acc - 1
    go  acc Constant {}  = acc - 1

-------------------------------------------------------------------------------
-- IfThenElse
-------------------------------------------------------------------------------

data TraceRewrite
    = TraceRewrite    -- ^ rewrite @trace@ applications with known arguments
    | TraceRemove     -- ^ remove @trace@ applications, replacing by no-op functions.
  deriving (Eq, Show)

data IfeRewrite
    = IfeRewrite
    | IfeRewriteMore
  deriving (Eq, Show)

-- | Apply rewrites using the facts about 'Known' terms.
--
-- >>> pp $ knownRewrites (Just TraceRewrite) (Just IfeRewrite) $ let_ "True" (RawTrue "t" "f") "True"
-- let* id = \ x -> x
--      ~id = \ ~ y -> y
--      ~~id = \ ~ ~ z -> z
--      const = \ u1 v1 -> u1
--      flipConst = \ u2 v2 -> v2
--      True = \ ~ true1 false1 -> true1
--      False = \ ~ true2 false2 -> false2
--      ~True = \ ~ ~ true3 false3 -> true3
--      ~False = \ ~ ~ true4 false4 -> false4
--      fstOf3 = \ m1 n1 p1 -> m1
--      sndOf3 = \ m2 n2 p2 -> n2
--      trdOf3 = \ m3 n3 p3 -> p3
--      EQ = \ ~ m4 n4 p4 -> m4
--      GT = \ ~ m5 n5 p5 -> n5
--      LT = \ ~ m6 n6 p6 -> p6
--      ~EQ = \ ~ ~ m7 n7 p7 -> m7
--      ~GT = \ ~ ~ m8 n8 p8 -> n8
--      ~LT = \ ~ ~ m9 n9 p9 -> p9
--      fix = \ f -> let* rec = \ rec0 arg -> f (rec0 rec0) arg in rec rec
--      zComb =
--        \ f_0 ->
--          let* x_0 = \ y_0 -> f_0 (\ u -> y_0 y_0 u)
--          in f_0 (\ v -> x_0 x_0 v)
-- in True
--
knownRewrites :: Ord a => Maybe TraceRewrite -> Maybe IfeRewrite -> Raw a n -> Raw a n
knownRewrites traceRewrite' ifeRewrite =
    L.over free Right >>>
    fixedpoint (addKnown >>> simplify) >>>
    rewriteAll (ifThenElseKnown ifeRewrite \/ traceRewrite) >>>
    removeKnown
  where
    traceRewrite :: Raw (Either Known a) n -> Maybe (Raw (Either Known a) n)
    traceRewrite = case traceRewrite' of
        Nothing           -> const Nothing
        Just TraceRewrite -> traceKnown
        Just TraceRemove  -> traceRemove

isDelayed :: Raw (Either Known a) n -> Maybe (Raw (Either Known a) n)
isDelayed (Delay t)                 = Just t
isDelayed (Known KnownDelayId)      = Just (Known KnownId)
isDelayed (Known KnownDelayDelayId) = Just (Known KnownDelayId)
isDelayed (Known KnownDelayTrue)    = Just (Known KnownTrue)
isDelayed (Known KnownDelayFalse)   = Just (Known KnownFalse)
isDelayed (Known KnownTrue)         = Just (Known KnownConst)
isDelayed (Known KnownFalse)        = Just (Known KnownFlipConst)
isDelayed (Known KnownEQ)           = Just (Known KnownFstOf3)
isDelayed (Known KnownGT)           = Just (Known KnownSndOf3)
isDelayed (Known KnownLT)           = Just (Known KnownTrdOf3)
isDelayed (Known KnownDelayEQ)      = Just (Known KnownEQ)
isDelayed (Known KnownDelayGT)      = Just (Known KnownGT)
isDelayed (Known KnownDelayLT)      = Just (Known KnownLT)
isDelayed (Known KnownDelayError)   = Just Error
isDelayed _                         = Nothing

addKnown :: Ord a => Raw (Either Known a) n -> Raw (Either Known a) n
addKnown = rewrite f where
    f :: Raw (Either Known a) n -> Maybe (Raw (Either Known a) n)
    f t | Just k <- isKnown t             = Just (Known k)
    -- what we match on might overlap:
    f (Lam _ctrue (Known KnownId))         = Just (Known KnownFlipConst)
    f (Delay (Lam _ctrue (Known KnownId))) = Just (Known KnownFalse)
    f (Delay (Known KnownId))              = Just (Known KnownDelayId)
    f (Delay (Known KnownDelayId))         = Just (Known KnownDelayDelayId)
    f (Delay (Known KnownConst))           = Just (Known KnownTrue)
    f (Delay (Known KnownFlipConst))       = Just (Known KnownFalse)
    f (Delay (Known KnownTrue))            = Just (Known KnownDelayTrue)
    f (Delay (Known KnownFalse))           = Just (Known KnownDelayFalse)
    f (Lam _ (Known KnownConst))           = Just (Known KnownSndOf3)
    f (Lam _ (Known KnownFlipConst))       = Just (Known KnownTrdOf3)
    f (Delay (Known KnownFstOf3))          = Just (Known KnownEQ)
    f (Delay (Known KnownSndOf3))          = Just (Known KnownGT)
    f (Delay (Known KnownTrdOf3))          = Just (Known KnownLT)
    f (Delay (Known KnownEQ))              = Just (Known KnownDelayEQ)
    f (Delay (Known KnownGT))              = Just (Known KnownDelayGT)
    f (Delay (Known KnownLT))              = Just (Known KnownDelayLT)

    f _ = Nothing

removeKnown :: Raw (Either Known a) n -> Raw a n
removeKnown t =
    knownLet KnownId $
    knownLet KnownDelayId $
    knownLet KnownDelayDelayId $
    knownLet KnownConst $
    knownLet KnownFlipConst $
    knownLet KnownTrue $
    knownLet KnownFalse $
    knownLet KnownDelayTrue $
    knownLet KnownDelayFalse $
    knownLet KnownFstOf3 $
    knownLet KnownSndOf3 $
    knownLet KnownTrdOf3 $
    knownLet KnownEQ $
    knownLet KnownGT $
    knownLet KnownLT $
    knownLet KnownDelayEQ $
    knownLet KnownDelayGT $
    knownLet KnownDelayLT $
    knownLet KnownFix $
    knownLet KnownZ $
    -- Delay Error is smaller rep then a variable.
    -- For uniswap contract the binding resulted in smaller fees, even size increased.
    rename (mkRen $ VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS . VS) t >>== \k -> case k of
        Right x                -> Free x
        Left KnownId           -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))))))))))))
        Left KnownDelayId      -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ))))))))))))))))))
        Left KnownDelayDelayId -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))))))))))
        Left KnownConst        -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ))))))))))))))))
        Left KnownFlipConst    -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))))))))
        Left KnownTrue         -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ))))))))))))))
        Left KnownFalse        -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))))))
        Left KnownDelayTrue    -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ))))))))))))
        Left KnownDelayFalse   -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))))
        Left KnownFstOf3       -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ))))))))))
        Left KnownSndOf3       -> Var (VS (VS (VS (VS (VS (VS (VS (VS (VS VZ)))))))))
        Left KnownTrdOf3       -> Var (VS (VS (VS (VS (VS (VS (VS (VS VZ))))))))
        Left KnownEQ           -> Var (VS (VS (VS (VS (VS (VS (VS VZ)))))))
        Left KnownGT           -> Var (VS (VS (VS (VS (VS (VS VZ))))))
        Left KnownLT           -> Var (VS (VS (VS (VS (VS VZ)))))
        Left KnownDelayEQ      -> Var (VS (VS (VS (VS VZ))))
        Left KnownDelayGT      -> Var (VS (VS (VS VZ)))
        Left KnownDelayLT      -> Var (VS (VS VZ))
        Left KnownFix          -> Var (VS VZ)
        Left KnownZ            -> Var VZ
        Left KnownDelayError   -> knownRaw KnownDelayError
        Left KnownIFE          -> knownRaw KnownIFE
        Left KnownTT           -> knownRaw KnownTT
        Left KnownTrace        -> knownRaw KnownTrace

knownLet :: Known -> Raw a (S n) -> Raw a n
knownLet k = Let (knownName k) (knownRaw k)

-- | Rewrite 'ifThenElse#' known patterns.
--
ifThenElseKnown :: Maybe IfeRewrite -> Raw (Either Known a) n -> Maybe (Raw (Either Known a) n)
ifThenElseKnown Nothing _ = Nothing

-- ifThenElse# ! p True False !  -->  ifThenElse ! p
ifThenElseKnown (Just IfeRewrite)
    (Force (Force (Known KnownIFE) :@ p :@ Known KnownTrue :@ Known KnownFalse))
    = Just $ Force (Known KnownIFE) :@ p

-- ifThenElse ! val True False  -->  \~ -> ifThenElse ! val
ifThenElseKnown (Just IfeRewrite)
    (Force (Known KnownIFE) :@ p :@ Known KnownTrue :@ Known KnownFalse)
    | isValue (const 0) p
    = Just $ Delay $ Force (Known KnownIFE) :@ p
-- this variant increases laziness, same as above, but unconditionally.
ifThenElseKnown (Just IfeRewriteMore)
    (Force (Known KnownIFE) :@ p :@ Known KnownTrue :@ Known KnownFalse)
    = Just $ Delay $ Force (Known KnownIFE) :@ p

-- ifThenElse# ! p False True ! x y  -->  ifThenElse ! p y x
ifThenElseKnown _
    (Force (Force (Known KnownIFE) :@ p :@ Known KnownFalse :@ Known KnownTrue) :@ ctrue :@ cfalse)
    = Just $ Force (Known KnownIFE) :@ p :@ cfalse :@ ctrue

ifThenElseKnown _ _ = Nothing

-- | Replace @trace#@ with @\ ~ p x -> x@.
traceRemove :: Raw (Either Known a) n -> Maybe (Raw (Either Known a) n)
traceRemove (Known KnownTrace) = Just (Known KnownFalse) -- False = @\ ~ p x -> x@
traceRemove _ = Nothing

-- | Rewrite @trace@ applications with known values.
--
-- @
-- trace# ! "must not remove tokens"# False ! val (\ ~ -> False)
-- @
traceKnown :: Raw (Either Known a) n -> Maybe (Raw (Either Known a) n)

-- trace# ! p (delay val) !             -->  trace# ! p val
traceKnown (Force (Force (Known KnownTrace) :@ p :@ v))
    | Just v' <- isDelayed v, isValue (const 0) v'
    = Just $ Force (Known KnownTrace) :@ p :@ v'

-- trace# ! p id x                      -->  trace# ! p (\ ~ -> x) !
traceKnown (Force (Known KnownTrace) :@ p :@ Known KnownId :@ x)
    = Just $ Force $ Force (Known KnownTrace) :@ p :@ Delay x

-- trace# ! p const val1 val2           -->  trace# ! p (\ ~ -> val1) !
traceKnown (Force (Known KnownTrace) :@ p :@ Known KnownConst :@ val1 :@ val2)
    | isValue (const 0) val2
    = Just $ Force $ Force (Known KnownTrace) :@ p :@ Delay val1

-- trace# ! p flipConst val1 val2       -->  trace# ! p (\ ~ -> val2) !
traceKnown (Force (Known KnownTrace) :@ p :@ Known KnownFlipConst :@ val1 :@ val2)
    | isValue (const 0) val1
    = Just $ Force $ Force (Known KnownTrace) :@ p :@ Delay val2

-- let thunk = trace# ! p val in body   --> trace# ! p (\ ~ -> body) !
traceKnown (Let _ (Force (Known KnownTrace) :@ p :@ val) body)
    | isValue (const 0) val, Just body' <- bound unusedVar body
    = Just $ Force $ Force (Known KnownTrace) :@ p :@ Delay body'

traceKnown _ = Nothing

-------------------------------------------------------------------------------
-- Inline used once
-------------------------------------------------------------------------------

-- | Inline bindings used at most once.
--
-- Note: this also does 'unusedBinding' rewrite.
--
-- >>> let term = let_ "x" "unused" "body"
-- >>> pp term
-- let* x = unused
-- in body
--
-- >>> pp $ inlineUsedOnce' term
-- body
--
-- >>> let term = let_ "x" "used" "x"
-- >>> pp term
-- let* x = used
-- in x
--
-- >>> pp $ inlineUsedOnce' term
-- used
--
-- >>> let term = let_ "x" "used" $ "f" :@ "x" :@ "x"
-- >>> pp term
-- let* x = used
-- in f x x
--
-- >>> pp $ inlineUsedOnce' term
-- let* x = used
-- in f x x
--
-- When bound term is an unsaturated application, we can inline it still:
--
-- >>> let term = let_ "f" (lams_ ["x","y","z"] $ "foo" :@ "x" :@ "y" :@ "z") $ let_ "used" ("f" :@ "bar" :@ "f") "used"
-- >>> pp term
-- let* f = \ x y z -> foo x y z
--      used = f bar f
-- in used
--
-- >>> pp $ inlineUsedOnce' term
-- let* f = \ x y z -> foo x y z
-- in f bar f
--
-- If bound value is used once and strictly, it's good reason to inline it:
--
-- >>> let term = let_ "f" ("foo" :@ "bar") $ "f" :@ "quu"
-- >>> pp term
-- let* f = foo bar
-- in f quu
--
-- >>> pp $ inlineUsedOnce' term
-- foo bar quu
--
inlineUsedOnce :: Bindings a n -> Raw a n -> Maybe (Raw a n)
inlineUsedOnce ctx (Let _n t s)
    | isValue (bindingArity ctx) t || VZ `isStrictIn` s
    , bound this s <= Const (Sum 1)
    = Just (instantiate1 t s)
  where
    this :: Var (S n) -> Const (Sum Int) (Var (S n))
    this VZ     = Const (Sum 1)
    this (VS _) = Const (Sum 0)

inlineUsedOnce _ _ = Nothing

-- | Rewrite using 'inlineUsedOnce'.
inlineUsedOnce' :: Ord a => Raw a n -> Raw a n
inlineUsedOnce' = rewriteWithBindings inlineUsedOnce

-------------------------------------------------------------------------------
-- Atomic transformations
-------------------------------------------------------------------------------

-- | Let-from-let.
--
-- >>> let term = let_ "x" (let_ "y" (delay_ "foo") (delay_ "bar")) ("body" :@ "x" :@ "z")
-- >>> pp term
-- let* x = let* y = \ ~ -> foo in \ ~ -> bar
-- in body x z
--
-- >>> pp $ rewrite letFromLet term
-- let* y = \ ~ -> foo
--      x = \ ~ -> bar
-- in body x z
--
-- This is done by 'simplify'.
--
-- >>> pp $ simplify term
-- let* y = \ ~ -> foo
--      x = \ ~ -> bar
-- in body x z
--
letFromLet :: Raw a n -> Maybe (Raw a n)
letFromLet (Let x (Let y foo bar) body) = Just $
    Let y foo $ Let x bar (bump body)
letFromLet _ = Nothing

-- | Force-Delay elimination.
--
-- >>> let term = force_ (delay_ "t")
-- >>> pp term
-- (\ ~ -> t) !
--
-- >>> pp $ rewrite forceDelay term
-- t
--
-- This is done by 'simplify', but exists so we can test
-- that compiled code doesn't have this kind of reductions.
--
-- >>> pp $ simplify term
-- t
--
forceDelay :: Raw a n -> Maybe (Raw a n)
forceDelay (Force (Delay t)) = Just t
forceDelay _                 = Nothing

-- | Unused binding elimination.
--
-- >>> let term = let_ "x" "unused" "body"
-- >>> pp term
-- let* x = unused
-- in body
--
-- >>> pp $ rewrite unusedBinding term
-- body
--
-- >>> let term = let_ "x" "used" "x"
-- >>> pp term
-- let* x = used
-- in x
--
-- >>> pp $ rewrite unusedBinding term
-- let* x = used
-- in x
--
unusedBinding :: Raw a n -> Maybe (Raw a n)
unusedBinding (Let _n t s) | isValue (const 0) t = bound unusedVar s
unusedBinding _                                  = Nothing

-- | 'Error' propagation.
--
-- >>> let term = Error :@ "foo" :@ "bar"
-- >>> pp term
-- ERROR foo bar
--
-- >>> pp $ rewriteWithBindings (appError AppErrorAll) term
-- ERROR
--
-- This is conservative, and is done bu 'simplify' already
--
-- >>> pp $ simplify term
-- ERROR
--
-- But also when 'Error' is an argument:
--
-- >>> let term = ("bar" :@ "foo") :@ Error
-- >>> pp term
-- bar foo ERROR
--
-- >>> pp $ rewriteWithBindings (appError AppErrorAll) term
-- ERROR
--
-- but
--
-- >>> pp $ simplify term
-- bar foo ERROR
--
appError :: AppError -> Bindings a n -> Raw a n -> Maybe (Raw a n)
appError _             _   (App Error _)   = Just Error
appError AppErrorAll   _   (App _ Error)   = Just Error
appError AppErrorValue ctx (App f Error)
    | isValue (bindingArity ctx) f              = Just Error
appError _             _   (Force Error)   = Just Error
appError _             _   (Let _ Error _) = Just Error
appError AppErrorAll   _   (Let _ _ Error) = Just Error
appError AppErrorValue ctx (Let _ t Error)
    | isValue (bindingArity ctx) t              = Just Error
appError _              _   _               = Nothing

data AppError
    = AppErrorValue  -- ^ rewrite @f Error@ to error when @f@ is a value.
    | AppErrorAll    -- ^ rewrite @f Error@ to @Error@ always.
  deriving (Eq, Show)

-- | Eta-reduce delay force if the term is a value.
--
-- >>> let term = delay_ (force_ "foo")
-- >>> pp term
-- \ ~ -> foo !
--
-- >>> pp $ rewriteWithBindings etaForce term
-- foo
--
-- Non-values are not reduced:
--
-- >>> let term = delay_ (force_ ("f" :@ "x"))
-- >>> pp term
-- \ ~ -> f x !
--
-- >>> pp $ rewriteWithBindings etaForce term
-- \ ~ -> f x !
--
etaForce :: Bindings a n -> Raw a n -> Maybe (Raw a n)
etaForce ctx (Delay (Force v)) | isValue (bindingArity ctx) v = Just v
etaForce _ _ = Nothing

-- | Eta reduce function.
--
-- >>> let term = lam_ "arg" $ "fun" :@ "arg"
-- >>> pp term
-- \ arg -> fun arg
--
-- >>> pp $ rewriteWithBindings etaFun term
-- fun
--
-- >>> let term = lams_ ["x","y","z"] $ "fun" :@ "x" :@ "y" :@ "z"
-- >>> pp term
-- \ x y z -> fun x y z
--
-- >>> pp $ rewriteWithBindings etaFun term
-- fun
--
-- Non-value functions are not reduced:
--
-- >>> let term = lam_ "arg" $ "g" :@ "y" :@ "arg"
-- >>> pp term
-- \ arg -> g y arg
--
-- >>> pp $ rewriteWithBindings etaFun term
-- \ arg -> g y arg
--
etaFun :: Bindings a n -> Raw a n -> Maybe (Raw a n)
etaFun _ctx (Lam _ (App f Var0))
    | isValue (const 0) f -- here using bindingArity ctx breaks fix !?
    , Just f' <- bound unusedVar f
    = Just f'
etaFun _ctx (Lam _ (Lam _ (f :@ Var1 :@ Var0)))
    | isValue (const 0) f
    , Just f' <- bound unusedVar2 f
    = Just f'
etaFun _ctx (Lam _ (Lam _ (Lam _ (f :@ Var2 :@ Var1 :@ Var0))))
    | isValue (const 0) f
    , Just f' <- bound unusedVar3 f
    = Just f'
etaFun _ _ = Nothing

-- | Lambda float.
--
-- >>> let term = lam_ "x" $ let_ "y" (lams_ ["z","w"] "z") $ "y" :@ "x"
-- >>> pp term
-- \ x -> let* y = \ z w -> z in y x
--
-- >>> pp $ rewriteWithBindings floatOutLambda term
-- let* y = \ z w -> z
-- in \ x -> y x
--
-- There might be @let@s in between,
-- we still float out through them.
--
-- >>> let term = lam_ "x" $ let_ "foo" ("f" :@ "x") $ let_ "bar" ("g" :@ "x") $ let_ "y" (lams_ ["z","w"] "z") $ "foo" :@ "bar" :@ "y"
-- >>> pp term
-- \ x -> let* foo = f x; bar = g x; y = \ z w -> z in foo bar y
--
-- >>> pp $ rewriteWithBindings floatOutLambda term
-- let* y = \ z w -> z
-- in \ x -> let* foo = f x; bar = g x in foo bar y
--
floatOutLambda :: forall n a. Bindings a n -> Raw a n -> Maybe (Raw a n)
floatOutLambda ctx (Lam n0 t0)
    = go unusedVar swap0 (Lam n0) t0
  where
    go :: (Var m -> Maybe (Var n))        -- whether term can be floated out, i.e. doesn't use local bindings
       -> (Var (S m) -> Var (S m))    -- renaming
       -> (Raw a (S m) -> Raw a (S n))  -- structure
       -> Raw a m                        -- term
       -> Maybe (Raw a n)
    go unused ren mk (Let n t s)
        | Just t' <- bound unused t
        , isValue (bindingArity ctx) t'
        = Just $ Let n t' (mk (rename (mkRen ren) s))

        | otherwise
        = go (unvar Nothing unused)
             (swap1 ren)
             (mk . Let n (rename (mkRen (ren . VS)) t))
             s

    go _ _ _ _ = Nothing

    swap0 :: Var (S (S m)) -> Var (S (S m))
    swap0 VZ      = VS VZ
    swap0 (VS VZ) = VZ
    swap0 v       = v

    swap1 :: (Var (S m) -> Var (S m)) -> Var (S (S m)) -> Var (S (S m))
    swap1 f VZ          = VS (f VZ)
    swap1 _ (VS VZ)     = VZ
    swap1 f (VS (VS n)) = VS (f (VS n))

floatOutLambda _ _ = Nothing

-- | Delay float.
--
-- >>> let term = delay_ $ let_ "y" "z" $ "y" :@ "x"
-- >>> pp term
-- \ ~ -> let* y = z in y x
--
-- >>> pp $ rewriteWithBindings floatOutDelay term
-- let* y = z
-- in \ ~ -> y x
--
-- >>> let term = delay_ $ let_ "fx" ("f" :@ "x") $ let_ "const" (lams_ ["y","z"] "y") $ "const" :@ "fx"
-- >>> pp term
-- \ ~ -> let* fx = f x; const = \ y z -> y in const fx
--
-- >>> pp $ rewriteWithBindings floatOutDelay term
-- let* const = \ y z -> y
-- in \ ~ -> let* fx = f x in const fx
--
floatOutDelay :: forall n a. Bindings a n -> Raw a n -> Maybe (Raw a n)
floatOutDelay ctx (Delay t0)
    = go Just id Delay t0
  where
    go :: (Var m -> Maybe (Var n))        -- whether term can be floated out, i.e. doesn't use local bindings
       -> (Var (S m) -> Var (S m))    -- renaming
       -> (Raw a (S m) -> Raw a (S n))  -- structure
       -> Raw a m                        -- term
       -> Maybe (Raw a n)
    go unused ren mk (Let n t s)
        | Just t' <- bound unused t
        , isValue (bindingArity ctx) t'
        = Just $ Let n t' (mk (rename (mkRen ren) s))

        | otherwise
        = go (unvar Nothing unused)
             (swap1 ren)
             (mk . Let n (rename (mkRen (ren . VS)) t))
             s
    go _ _ _ _ = Nothing

    swap1 :: (Var (S m) -> Var (S m)) -> Var (S (S m)) -> Var (S (S m))
    swap1 f VZ          = VS (f VZ)
    swap1 _ (VS VZ)     = VZ
    swap1 f (VS (VS n)) = VS (f (VS n))

floatOutDelay _ _ = Nothing

-- | App argument float.
--
-- Let is also floated from the argument.
-- This is not precisely semantics preserving as it may change order
-- of trace
--
-- >>> let term = "f" :@ "arg" :@ let_ "n" (delay_ "def") "x"
-- >>> pp term
-- f arg (let* n = \ ~ -> def in x)
--
-- >>> pp $ rewriteWithBindings (floatOutAppArg FloatOutAppArgValue) term
-- let* n = \ ~ -> def
-- in f arg x
--
-- >>> pp $ rewriteWithBindings (floatOutAppArg FloatOutAppArgAll) term
-- let* n = \ ~ -> def
-- in f arg x
--
-- Floats out of if then else too
--
-- >>> let term = ite_ (let_ "n" (delay_ ("foo" :@ "bar")) ("n" :@ "n")) "consequence" "alternative"
-- >>> pp term
--ifThenElse# ! (let* n = \ ~ -> foo bar in n n) consequence alternative
--
-- >>> pp $ rewriteWithBindings (floatOutAppArg FloatOutAppArgAll) term
-- (let* n = \ ~ -> foo bar in ifThenElse# ! (n n)) consequence alternative
--
-- >>> pp $ simplify $ rewriteWithBindings (floatOutAppArg FloatOutAppArgAll) term
-- let* n = \ ~ -> foo bar
-- in ifThenElse# ! (n n) consequence alternative
--
floatOutAppArg :: FloatOutAppArg -> Bindings a n -> Raw a n -> Maybe (Raw a n)
floatOutAppArg FloatOutAppArgValue ctx (App f (Let n t s))
    |  isValue (bindingArity ctx) f
    || isValue (bindingArity ctx) t
    = Just (Let n t (App (weaken f) s))
floatOutAppArg FloatOutAppArgAll   _ (App f (Let n t s))
    = Just (Let n t (App (weaken f) s))
floatOutAppArg _ _ _ = Nothing

data FloatOutAppArg
    = FloatOutAppArgValue  -- ^ rewrite @f (let n t s)@ to @let n t (f s)@ when f is a value
    | FloatOutAppArgAll    -- ^ rewrite always
  deriving (Eq, Show)

-- | Replace if-then-else lambdas with delays
--
-- >>> let term = ite_ "condition" (lam_ "ds" "foo") (lam_ "ds" "bar") :@ "tt"
-- >>> pp term
-- ifThenElse# ! condition (\ ds -> foo) (\ ds_0 -> bar) tt
--
-- >>> pp $ rewriteWithBindings ifLambda term
-- ifThenElse# ! condition (\ ~ -> foo) (\ ~ -> bar) !
--
ifLambda :: Bindings a n -> Raw a n -> Maybe (Raw a n)
ifLambda ctx (p@(Force (Builtin IfThenElse) :@ _) :@ Lam _n1 t1 :@ Lam _n2 t2 :@ v)
    | isValue (bindingArity ctx) v
    , Just t1' <- bound unusedVar t1
    , Just t2' <- bound unusedVar t2
    = Just $ Force $ p :@ Delay t1' :@ Delay t2'

ifLambda _ _ = Nothing

-- | Let zero
--
-- >>> let term = let_ "f" (lams_ ["x","y"] $ "x" :@ "y") $ "f" :@ "foo" :@ "bar"
-- >>> pp term
-- let* f = \ x y -> x y
-- in f foo bar
--
-- >>> pp $ rewriteWithBindings letZero term
-- (\ x y -> x y) foo bar
--
letZero :: Bindings a n -> Raw a n -> Maybe (Raw a n)
letZero _ (Let _n t s)
    | (Var VZ, args) <- peelApp s
    , Just args' <- traverse (traverseArgTerm (bound unusedVar)) args
    = Just (appArgs_ t args')
letZero _ _ = Nothing

-- | Commute equals so the constants are the first arguments.
commEquals :: Bindings a n -> Raw a n -> Maybe (Raw a n)
commEquals _ (Builtin EqualsInteger :@ Constant _ :@ _) =
    Nothing
commEquals _ (Builtin EqualsInteger :@ x          :@ y@(Constant _)) =
    Just $ Builtin EqualsInteger :@ y :@ x
commEquals _ _ = Nothing

-- | Inline constants.
--
inlineConstants :: Bindings a n -> Raw a n -> Maybe (Raw a n)
inlineConstants _ (Let _n t@(Constant _) s) = Just (instantiate1 t s)
inlineConstants _ _                         = Nothing

-------------------------------------------------------------------------------
-- Inconsistent
-------------------------------------------------------------------------------

-- | See https://github.com/input-output-hk/plutus/issues/4183
forcedBuiltin :: Raw a n -> Maybe (Raw a n)
forcedBuiltin (Force b@Builtin {}) = Just b
forcedBuiltin _                    = Nothing
