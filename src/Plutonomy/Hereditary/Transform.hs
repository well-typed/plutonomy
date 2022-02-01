module Plutonomy.Hereditary.Transform (
    -- * Transformations
    splitDelay, splitDelay',
    inlineSaturated, inlineSaturated', inlineSize,
    commonBindings,
    -- * Single rewrites
    inlineConstants,
    inlineUsedOnce,
    letZero,
    appError,
    etaForce,
    etaFun,
    ifLambda,
    floatOutLambda,
    floatOutAppArg,
    floatOutDelay,
    commBuiltin,
) where

import Control.Applicative (Const (..))
import Data.Bifunctor      (bimap)
import Data.Foldable       (foldl')
import Data.Map.Strict     (Map)
import Data.Monoid         (Sum (..))
import Data.Sequence       (pattern (:<|), pattern (:|>))
import PlutusCore.Default  (DefaultFun (EqualsInteger, IfThenElse))
import Subst
       (Nat (..), Rename (..), Var (..), Vars (..), bump, instantiate1, mkRen, rename, unusedVar, unusedVar2, unusedVar3, unvar,
       weaken)

import qualified Data.Map.Strict as Map
import qualified Data.Sequence   as Seq

import Plutonomy.Hereditary
import Plutonomy.Hereditary.Rewrite
import Plutonomy.Name
import Plutonomy.Raw.Transform      (AppError (..), FloatOutAppArg (..))


-- $setup
-- >>> import Plutonomy.MissingH
-- >>> import Subst
-- >>> import Plutonomy.Hereditary
-- >>> import Plutonomy.Hereditary.Rewrite
-- >>> import Plutonomy.Raw.Transform      (AppError (..), FloatOutAppArg (..))
-- >>> import Plutonomy.Pretty (prettyRaw)
-- >>> import Data.Text (Text)
-- >>> import Control.Monad (forM_)
-- >>> import PlutusCore.Default (DefaultFun (..))
-- >>> import qualified Prettyprinter as PP
--
-- >>> let pp t = prettyRaw PP.pretty (toRaw (t :: Term Text Z))

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
-- let* fix!! = \ x -> x x x
--      fix! = \ ~ -> fix!!
--      fix = \ ~ -> fix!
-- in fix ! ! f
--
-- Unused bindings will be removed by other passes.
--
-- >>> pp $ fixedpoint (inlineSaturated' 0) $ splitDelay' term
-- let* fix!! = \ x -> x x x
--      fix! = \ ~ -> fix!!
--      fix = \ ~ -> fix!
-- in fix!! f
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
-- let* res! = f arg1 arg2
--      res = \ ~ -> res!
--      foo = g bar (res !)
-- in body
--
-- >>> pp $ fixedpoint (inlineSaturated' 0) $ splitDelay' term
-- let* res! = f arg1 arg2
--      res = \ ~ -> res!
--      foo = g bar res!
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
--      res! = f arg1 arg2
--      res = \ ~ -> res!
-- in body
--
splitDelay :: Definitions a n -> Term a n -> Maybe (Term a n)
splitDelay _ctx (Let _n (Delay (Var _)) _s) = Nothing
splitDelay  ctx (Let  n (Delay (Defn t)) s)
    | isValue (definitionArity ctx) (const 100) (Defn t) || VZ `isForcedIn` s
    = Just $ Let (forcedName n) t $ Let n (Delay (Var VZ)) $ bump s

-- This destroyes some sharing atm
-- splitDelay  ctx (Let  n (Lam n' (Defn t')) s)
--     | Just t <- bound unusedVar t'
--     , isValue (definitionArity ctx) (const 100) (Defn t) || VZ `isForcedIn` s
--     = Just $ Let (unusedName n) t $ Let n (Lam n' (Var (VS VZ))) $ bump s

splitDelay _ _ = Nothing

-- | Rewrite using 'splitDelay'.
splitDelay' :: Ord a => Term a n -> Term a n
splitDelay' = rewriteWithDefinitions splitDelay

-------------------------------------------------------------------------------
-- Variable usage traversals
-------------------------------------------------------------------------------

isForcedIn :: Var n -> Term a n -> Bool
isForcedIn x (Defn d)     = isForcedInDefn x d
isForcedIn _ Error        = False
isForcedIn x (Let _n t s) = isForcedInDefn x t || isForcedIn (VS x) s

isForcedInDefn :: Var n -> Defn a n -> Bool
isForcedInDefn x (Neutral h sp) = isForcedInHead x h sp || any (isForcedInElim x) sp
isForcedInDefn _ (Lam _ _ )     = False
isForcedInDefn _ (Delay _)      = False
isForcedInDefn _ (Constant _)   = False

isForcedInHead :: Var n -> Head a n -> Spine a n -> Bool
isForcedInHead x (HeadVar y) sp = x == y && not (null sp)
isForcedInHead _ _           _  = False

isForcedInElim :: Var n -> Elim a n -> Bool
isForcedInElim _ Force   = False
isForcedInElim x (App t) = isForcedIn x t

isStrictIn :: Var n -> Term a n -> Bool
isStrictIn x (Defn d)     = isStrictInDefn x d
isStrictIn _ Error        = False
isStrictIn x (Let _n t s) = isStrictInDefn x t || isStrictIn (VS x) s

isStrictInDefn :: Var n -> Defn a n -> Bool
isStrictInDefn x (Neutral h sp) = isStrictInHead x h || any (isStrictInElim x) sp
isStrictInDefn _ (Lam _ _ )     = False
isStrictInDefn _ (Delay _)      = False
isStrictInDefn _ (Constant _)   = False

isStrictInHead :: Var n -> Head a n -> Bool
isStrictInHead x (HeadVar y) = x == y
isStrictInHead _ _           = False

isStrictInElim :: Var n -> Elim a n -> Bool
isStrictInElim _ Force   = False
isStrictInElim x (App t) = isStrictIn x t

-------------------------------------------------------------------------------
-- Inline saturated
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
-- in foo
--
-- TODO:
-- -- >>> pp $ rewriteWithDefinitions inlineUsedOnce $ simplify $ inlineSaturated' 0 term
-- -- foo
--
-- An example with @ERROR@:
--
-- >>> let term = let_ "const" (lam_ "x" $ lam_ "y" "x") ("const" :@ "foo" :@ Error)
-- >>> pp $ inlineSaturated' 0 term
-- let* const = \ x y -> x
-- in ERROR
--
-- TODO:
-- -- >>> pp $ rewriteWithDefinitions inlineUsedOnce $ inlineSaturated' 0 term
-- -- ERROR
--
inlineSaturated' :: Ord a => Integer -> Term a n -> Term a n
inlineSaturated' size = rewriteWithDefinitions (inlineSaturated size) where

inlineSaturated :: Ord a => Integer -> Definitions a m -> Term a m -> Maybe (Term a m)
inlineSaturated size ctx (Defn (Neutral (HeadVar f) args))
    | Just (DefnWithArity a f') <- definitionLookup ctx f
    , 0 < a, a <= length args
    , inlineSize (Defn f') >= size
    = Just (neutral_ (Defn f') args)

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
-- -6
--
-- (TODO: why that returned -2)?
--
inlineSize :: Term a n -> Integer
inlineSize term = top 1 term where
    top :: Integer -> Term a n -> Integer
    top !acc (Defn (Lam _n t)) = top (2 + acc) t
    top !acc (Defn (Delay t))  = top (1 + acc) t
    top !acc t                 = go acc t

    go :: Integer -> Term a n -> Integer
    go  acc (Defn d)       = goD acc d
    go  acc Error          = acc
    go  acc (Let _n t s)   = go (goD (acc - 1) t) s

    goD :: Integer -> Defn a n -> Integer
    goD acc (Neutral _ xs) = foldl' goE (acc - 1) xs
    goD acc (Lam _n t)     = go (acc - 1) t
    goD acc (Delay t)      = go (acc - 1) t
    goD acc Constant {}    = acc - 1

    goE :: Integer -> Elim a n -> Integer
    goE acc Force          = acc - 1
    goE acc (App t)        = go (acc - 1) t

-------------------------------------------------------------------------------
-- CSE: Common bindings
-------------------------------------------------------------------------------

-- | Combine common bindings.
--
-- >>> let term = let_ "x" (delay_ "foo") $ let_ "y" (delay_ "foo") $ "f" :@ "x" :@ "y"
-- >>> pp term
-- let* x = \ ~ -> foo
--      y = \ ~ -> foo
-- in f x y
--
-- >>> pp $ commonBindings term
-- let* x = \ ~ -> foo
-- in f x x
--
-- Also if the if the same term is used in the body of let,
-- we use the variable:
--
-- TODO:
--
-- >> let term = let_ "x" (delay_ "foo") $ delay_ "foo"
-- >> pp term
-- let* x = \ ~ -> foo
-- in \ ~ -> foo
--
-- >> pp $ commonBindings term
-- let* x = \ ~ -> foo
-- in x
--
-- This is done only if we are binding a value.
--
commonBindings :: forall n a. Ord a => Term a n -> Term a n
commonBindings = rewriteWith f onLet (DefnToVar Map.empty) where
    onLet :: Name -> Defn a m -> DefnToVar a m -> DefnToVar a (S m)
    onLet _ t ctx
        | isValue (const 0) (const 0) (Defn t)
        = DefnToVar $ Map.insert (weaken t) VZ (unDefnToVar ctx')

        | otherwise
        = ctx'
      where
        ctx' = weaken ctx

    f :: DefnToVar a m -> Term a m -> Maybe (Term a m)
    f (DefnToVar ctx) (Let _n t s)
        | isValue (const 0) (const 0) (Defn t)
        , Just x <- Map.lookup t ctx
        = Just (instantiate1 (Var x) s)

    -- f (DefnToVar ctx) (Defn t)
    --     | isValue (const 0) (const 0) (Defn t)
    --     , Just x <- Map.lookup t ctx
    --     = Just (Var x)

    f _ _ = Nothing

newtype DefnToVar a n = DefnToVar { unDefnToVar :: Map (Defn a n) (Var n) }

instance Ord a => Rename (DefnToVar a) where
    r <@> DefnToVar m = DefnToVar $ Map.fromList . map (bimap (rename r) (rename r)) . Map.toList $ m

-------------------------------------------------------------------------------
-- Simple rewrites
-------------------------------------------------------------------------------

-- | Inline bindings used at most once.
--
-- >>> let term = let_ "x" (delay_ "unused") "body"
-- >>> pp term
-- let* x = \ ~ -> unused
-- in body
--
-- >>> pp $ rewriteWithDefinitions inlineUsedOnce term
-- body
--
-- >>> let term = let_ "x" (delay_ "used") ("f" :@ "x")
-- >>> pp term
-- let* x = \ ~ -> used
-- in f x
--
-- >>> pp $ rewriteWithDefinitions inlineUsedOnce term
-- f (\ ~ -> used)
--
-- >>> let term = let_ "x" (delay_ "used") $ "f" :@ "x" :@ "x"
-- >>> pp term
-- let* x = \ ~ -> used
-- in f x x
--
-- >>> pp $ rewriteWithDefinitions inlineUsedOnce term
-- let* x = \ ~ -> used
-- in f x x
--
-- When bound term is an unsaturated application, we can inline it still:
--
-- >>> let term = let_ "f" (lams_ ["x","y","z"] $ "foo" :@ "x" :@ "y" :@ "z") $ let_ "used" ("f" :@ "bar" :@ "f") (delay_ "used")
-- >>> pp term
-- let* f = \ x y z -> foo x y z
--      used = f bar f
-- in \ ~ -> used
--
-- >>> pp $ rewriteWithDefinitions inlineUsedOnce term
-- let* f = \ x y z -> foo x y z
-- in \ ~ -> f bar f
--
-- If bound value is used once and strictly, it's good reason to inline it:
--
-- >>> let term = let_ "f" ("foo" :@ "bar") $ "f" :@ "quu"
-- >>> pp term
-- let* f = foo bar
-- in f quu
--
-- >>> pp $ rewriteWithDefinitions inlineUsedOnce term
-- foo bar quu
--
inlineUsedOnce :: Definitions a n -> Term a n -> Maybe (Term a n)
inlineUsedOnce ctx (Let _n t s)
    | isValue (definitionArity ctx) (const 0) (Defn t) || VZ `isStrictIn` s
    , bound this s <= Const (Sum 1)
    = Just (instantiate1 (Defn t) s)
  where
    this :: Var (S n) -> Const (Sum Int) (Var (S n))
    this VZ     = Const (Sum 1)
    this (VS _) = Const (Sum 0)
inlineUsedOnce _ _ = Nothing


-- | 'Error' propagation.
--
-- >>> let term = Error :@ "foo" :@ "bar"
-- >>> pp term
-- ERROR
--
-- But also when 'Error' is an argument:
--
-- >>> let term = ("bar" :@ "foo") :@ Error
-- >>> pp term
-- bar foo ERROR
--
-- >>> pp $ rewriteWithDefinitions (appError AppErrorValue) term
-- bar foo ERROR
--
-- >>> pp $ rewriteWithDefinitions (appError AppErrorAll) term
-- ERROR
--

-- |
--
-- >>> let term = let_ "f" (delay_ "ff") ("f" :@ Error)
-- >>> pp term
-- let* f = \ ~ -> ff
-- in f ERROR
--
-- >>> pp $ rewriteWithDefinitions (appError AppErrorValue) term
-- let* f = \ ~ -> ff
-- in ERROR
--
-- >>> pp $ rewriteWithDefinitions (appError AppErrorAll) term
-- let* f = \ ~ -> ff
-- in ERROR
--
appError :: AppError -> Definitions a n -> Term a n -> Maybe (Term a n)
appError AppErrorValue ctx (Defn (Neutral h sp))
    | (sp', App Error :<| _) <- Seq.breakl isErrorElim sp
    , isValue (definitionArity ctx) (const 0) (Defn (Neutral h sp'))
    = Just Error
appError AppErrorAll   _   (Defn (Neutral _ sp))
    | any isErrorElim sp
    = Just Error
appError _ _ _ = Nothing

-- | Let zero
--
-- >>> let term = let_ "f" (lams_ ["x","y"] $ "y" :@ "x") $ "f" :@ "foo" :@ "bar"
-- >>> pp term
-- let* f = \ x y -> y x
-- in f foo bar
--
-- >>> pp $ rewrite letZero term
-- bar foo
--
letZero :: Term a n -> Maybe (Term a n)
letZero (Let _n t (Defn (Neutral (HeadVar VZ) sp)))
    | Just sp' <- traverse (elimVars unusedVar pure) sp
    = Just (neutral_ (Defn t) sp')
letZero _ = Nothing

-- | Eta-reduce delay force if the term is a value.
--
-- >>> let term = delay_ (force_ "foo")
-- >>> pp term
-- \ ~ -> foo !
--
-- >>> pp $ rewriteWithDefinitions etaForce term
-- foo
--
-- Non-values are not reduced:
--
-- >>> let term = delay_ (force_ ("f" :@ "x"))
-- >>> pp term
-- \ ~ -> f x !
--
-- >>> pp $ rewriteWithDefinitions etaForce term
-- \ ~ -> f x !
--
etaForce :: Definitions a n -> Term a n -> Maybe (Term a n)
etaForce ctx (Defn (Delay (Defn (Neutral h (ts :|> Force)))))
    | isValue (definitionArity ctx) (const 0) v
    = Just v
  where
    v = Defn (Neutral h ts)
etaForce _ _ = Nothing

-- | Eta reduce function.
--
-- >>> let term = lam_ "arg" $ "fun" :@ "arg"
-- >>> pp term
-- \ arg -> fun arg
--
-- >>> pp $ rewriteWithDefinitions etaFun term
-- fun
--
-- >>> let term = lams_ ["x","y","z"] $ "fun" :@ "x" :@ "y" :@ "z"
-- >>> pp term
-- \ x y z -> fun x y z
--
-- >>> pp $ rewriteWithDefinitions etaFun term
-- fun
--
-- Non-value functions are not reduced:
--
-- >>> let term = lam_ "arg" $ "g" :@ "y" :@ "arg"
-- >>> pp term
-- \ arg -> g y arg
--
-- >>> pp $ rewriteWithDefinitions etaFun term
-- \ arg -> g y arg
--
etaFun :: Definitions a n -> Term a n -> Maybe (Term a n)
etaFun _ctx (Defn (Lam _n (f :@ Var0)))
    | isValue (const 0) (const 0) f -- TODO: using definitionArity breaks fix !?
    , Just f' <- bound unusedVar f
    = Just f'
etaFun _ctx (Defn (Lam _ (Defn (Lam _ (f :@ Var1 :@ Var0)))))
    | isValue (const 0) (const 0) f
    , Just f' <- bound unusedVar2 f
    = Just f'
etaFun _ctx (Defn (Lam _ (Defn (Lam _ (Defn (Lam _ (f :@ Var2 :@ Var1 :@ Var0)))))))
    | isValue (const 0) (const 0) f
    , Just f' <- bound unusedVar3 f
    = Just f'
etaFun _ _ = Nothing

-- | Replace if-then-else lambdas with delays
--
-- >>> let term = force_ ite_ :@ "condition" :@ lam_ "ds" "foo" :@ lam_ "ds" "bar" :@ "tt"
-- >>> pp term
-- ifThenElse# ! condition (\ ds -> foo) (\ ds_0 -> bar) tt
--
-- >>> pp $ rewriteWithDefinitions ifLambda term
-- ifThenElse# ! condition (\ ~ -> foo) (\ ~ -> bar) !
--
ifLambda :: Definitions a n -> Term a n -> Maybe (Term a n)
ifLambda ctx (Defn (Neutral (HeadBuiltin IfThenElse) (Force :<| App c :<| App (Defn (Lam _n1 t1)) :<| App (Defn (Lam _n2 t2)) :<| App v :<| sp)))
    | isValue (definitionArity ctx) (const 0) v
    , Just t1' <- bound unusedVar t1
    , Just t2' <- bound unusedVar t2
    = Just $ Defn (Neutral (HeadBuiltin IfThenElse) (Force :<| App c :<| App (Defn (Delay t1')) :<| App (Defn (Delay t2')) :<| Force :<| sp))
ifLambda _ _ = Nothing

-- | Lambda float.
--
-- >>> let term = lam_ "x" $ let_ "y" (lams_ ["z","w"] "z") $ "y" :@ "x"
-- >>> pp term
-- \ x -> let* y = \ z w -> z in y x
--
-- >>> pp $ rewriteWithDefinitions floatOutLambda term
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
-- >>> pp $ rewriteWithDefinitions floatOutLambda term
-- let* y = \ z w -> z
-- in \ x -> let* foo = f x; bar = g x in foo bar y
--
floatOutLambda :: forall n a. Definitions a n -> Term a n -> Maybe (Term a n)
floatOutLambda ctx (Defn (Lam n0 t0)) = go unusedVar swap0 (Defn . Lam n0) t0
  where
    go :: (Var m -> Maybe (Var n))        -- whether term can be floated out, i.e. doesn't use local bindings
       -> (Var (S m) -> Var (S m))        -- renaming
       -> (Term a (S m) -> Term a (S n))  -- structure
       -> Term a m                        -- term
       -> Maybe (Term a n)
    go unused ren mk (Let n t s)
        | Just t' <- defnVars unused pure t
        , isValue (definitionArity ctx) (const 0) (Defn t')
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
-- >>> let term = delay_ $ let_ "y" (delay_ "z") $ "y" :@ "x"
-- >>> pp term
-- \ ~ -> let* y = \ ~ -> z in y x
--
-- >>> pp $ rewriteWithDefinitions floatOutDelay term
-- let* y = \ ~ -> z
-- in \ ~ -> y x
--
-- >>> let term = delay_ $ let_ "fx" ("f" :@ "x") $ let_ "const" (lams_ ["y","z"] "y") $ "const" :@ "fx"
-- >>> pp term
-- \ ~ -> let* fx = f x; const = \ y z -> y in const fx
--
-- >>> pp $ rewriteWithDefinitions floatOutDelay term
-- let* const = \ y z -> y
-- in \ ~ -> let* fx = f x in const fx
--
floatOutDelay :: forall n a. Definitions a n -> Term a n -> Maybe (Term a n)
floatOutDelay ctx (Defn (Delay t0)) = go Just id (Defn . Delay) t0
  where
    go :: (Var m -> Maybe (Var n))        -- whether term can be floated out, i.e. doesn't use local bindings
       -> (Var (S m) -> Var (S m))        -- renaming
       -> (Term a (S m) -> Term a (S n))  -- structure
       -> Term a m                        -- term
       -> Maybe (Term a n)
    go unused ren mk (Let n t s)
        | Just t' <- defnVars unused pure t
        , isValue (definitionArity ctx) (const 0) (Defn t')
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
-- >>> pp $ rewriteWithDefinitions (floatOutAppArg FloatOutAppArgValue) term
-- let* n = \ ~ -> def
-- in f arg x
--
-- >>> pp $ rewriteWithDefinitions (floatOutAppArg FloatOutAppArgAll) term
-- let* n = \ ~ -> def
-- in f arg x
--
-- Floats out of if then else too
--
-- >>> let term = force_ ite_  :@ let_ "n" (delay_ ("foo" :@ "bar")) ("n" :@ "n") :@ "consequence" :@ "alternative"
-- >>> pp term
--ifThenElse# ! (let* n = \ ~ -> foo bar in n n) consequence alternative
--
-- >>> pp $ rewriteWithDefinitions (floatOutAppArg FloatOutAppArgAll) term
-- let* n = \ ~ -> foo bar
-- in ifThenElse# ! (n n) consequence alternative
--
floatOutAppArg :: forall a n. FloatOutAppArg -> Definitions a n -> Term a n -> Maybe (Term a n)
floatOutAppArg FloatOutAppArgValue ctx0 (Defn (Neutral h sp)) =
    go0 ctx0 id (Defn (Neutral h Seq.Empty)) sp
  where
    go0 :: Definitions a m -> (Term a m -> Term a n) -> Term a m -> Spine a m -> Maybe (Term a n)
    go0 ctx mk f (App (Let n t s) :<| xs)
        |  isValue (definitionArity ctx) (const 0) f
        || isValue (definitionArity ctx) (const 0) (Defn t)
        = go (definitionsOnLet n t ctx) (mk . Let n t) (weaken f :@ s) (fmap weaken xs)
    go0 ctx mk f (x :<| xs) = go0 ctx mk (elim_ f x) xs
    go0 _   _  _ Seq.Empty  = Nothing

    go :: Definitions a m -> (Term a m -> Term a n) -> Term a m -> Spine a m -> Maybe (Term a n)
    go ctx mk f (App (Let n t s) :<| xs)
        |  isValue (definitionArity ctx) (const 0) f
        || isValue (definitionArity ctx) (const 0) (Defn t)
        = go (definitionsOnLet n t ctx) (mk . Let n t) (weaken f :@ s) (fmap weaken xs)
    go ctx mk f (x :<| xs) = go ctx mk (elim_ f x) xs
    go _   mk f Seq.Empty  = Just (mk f)

floatOutAppArg FloatOutAppArgAll _ctx (Defn (Neutral h sp)) =
    go0 id (Defn (Neutral h Seq.Empty)) sp
  where
    go0 :: (Term a m -> Term a n) -> Term a m -> Spine a m -> Maybe (Term a n)
    go0 mk f (App (Let n t s) :<| xs) = go (mk . Let n t) (weaken f :@ s) (fmap weaken xs)
    go0 mk f (x :<| xs)               = go0 mk (elim_ f x) xs
    go0 _  _ Seq.Empty                = Nothing

    go :: (Term a m -> Term a n) -> Term a m -> Spine a m -> Maybe (Term a n)
    go mk f (App (Let n t s) :<| xs) = go (mk . Let n t) (weaken f :@ s) (fmap weaken xs)
    go mk f (x :<| xs)               = go mk (elim_ f x) xs
    go mk f Seq.Empty                = Just (mk f)

floatOutAppArg _ _ _ = Nothing

-- | Commute commutative builtins so the constants are the first arguments.
commBuiltin :: Term a n -> Maybe (Term a n)
commBuiltin (Defn (Neutral (HeadBuiltin EqualsInteger) (App (Defn (Constant _)) :<| _))) =
    Nothing
commBuiltin (Defn (Neutral (HeadBuiltin EqualsInteger) (x :<| y@(App (Defn (Constant _))) :<| sp))) =
    Just $ Defn $ Neutral (HeadBuiltin EqualsInteger) (y :<| x :<| sp)
commBuiltin _ = Nothing

-- | Inline constants.
--
inlineConstants :: Term a n -> Maybe (Term a n)
inlineConstants (Let _n t@(Constant _) s) = Just (instantiate1 (Defn t) s)
inlineConstants _                         = Nothing
