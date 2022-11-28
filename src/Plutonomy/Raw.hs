{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}
module Plutonomy.Raw where

import Data.Kind          (Type)
import Data.List          (foldl')
import Data.String        (IsString (..))
import Data.Text          (Text)
import Data.Void          (Void)
import PlutusCore.Default (DefaultFun (..))

import Plutonomy.Builtins
import Plutonomy.Constant
import Plutonomy.Name
import Subst

-- $setup
-- >>> import Plutonomy
-- >>> import Data.Text (Text)
-- >>> import qualified Prettyprinter as PP
-- >>> import PlutusCore.Default (DefaultFun (..))
-- >>> let pp t = prettyRaw PP.pretty (t :: Raw Text Z)

-- | Raw term representation.
--
-- Closely resembles the @plutus-core@ structure,
-- but in addition we have a constructor for @let@.
--
data Raw (a :: Type) (n :: Nat)
    = Var (Var n)
    | Free a
    | Lam Name (Raw a (S n))
    | App (Raw a n) (Raw a n)
    | Force (Raw a n)
    | Delay (Raw a n)
    | Constant Constant
    | Builtin DefaultFun
    | Error

    | Let Name (Raw a n) (Raw a (S n))  -- ^ Extra constructor: @let@: @(\x -> t) s@ can be reduced immediately to @let@, but what follows then depends.
  deriving (Eq, Ord, Show)

type ClosedRaw = Raw Void Z

instance IsString a => IsString (Raw a n) where
    fromString = Free . fromString

instance Rename (Raw a) where
    (<@>) = renameDefault

instance Vars (Raw a) where
    var = Var

instance Subst (Raw a) where
    subst  sub (Var x      ) = substVar sub x
    subst _sub (Free x     ) = Free x
    subst  sub (Lam n b    ) = Lam n (subst (liftSub sub) b)
    subst  sub (App f t    ) = App (subst sub f) (subst sub t)
    subst  sub (Force t    ) = Force (subst sub t)
    subst  sub (Delay t    ) = Delay (subst sub t)
    subst _sub (Constant c ) = Constant c
    subst _sub (Builtin b  ) = Builtin b
    subst _sub (Error      ) = Error
    subst  sub (Let n t s  ) = Let n (subst sub t) (subst (liftSub sub) s)

instance Free Raw where
    ret = Free

    vars f _ (Var x )      = Var <$> f x
    vars _ g (Free x)      = Free <$> g x
    vars f g (Lam n b    ) = Lam n <$> vars f' g b where
        f' VZ     = pure VZ
        f' (VS x) = VS <$> f x
    vars f g (App h t    ) = App <$> vars f g h <*> vars f g t
    vars f g (Force t    ) = Force <$> vars f g t
    vars f g (Delay t    ) = Delay <$> vars f g t
    vars _ _ (Constant c ) = pure (Constant c)
    vars _ _ (Builtin b  ) = pure (Builtin b)
    vars _ _ (Error      ) = pure Error
    vars f g (Let n t s  ) = Let n <$> vars f g t <*> vars f' g s where
        f' VZ     = pure VZ
        f' (VS x) = VS <$> f x

    Var x      >>== _ = Var x
    Free x     >>== k = k x
    Lam n b    >>== k = Lam n (b >>== weaken . k)
    App f t    >>== k = App (f >>== k) (t >>== k)
    Force t    >>== k = Force (t >>== k)
    Delay t    >>== k = Delay (t >>== k)
    Constant c >>== _ = Constant c
    Builtin b  >>== _ = Builtin b
    Error      >>== _ = Error
    Let n t s  >>== k = Let n (t >>== k) (s >>== weaken . k)

-------------------------------------------------------------------------------
-- Patterns
-------------------------------------------------------------------------------

pattern Var0 :: Raw a (S n)
pattern Var0 = Var V0

pattern Var1 :: Raw a (S (S n))
pattern Var1 = Var V1

pattern Var2 :: Raw a (S (S (S n)))
pattern Var2 = Var V2

-------------------------------------------------------------------------------
-- Value
-------------------------------------------------------------------------------

-- | Applications, Forcing terms, 'Let' and 'Error' are not values.
--
-- Unsaturated applications of builtins are also values.
--
-- >>> isValue (const 0) (force_ trace_ :@ str_ "err")
-- True
--
-- >>> isValue (const 0) (force_ trace_ :@ str_ "err" :@ tt_)
-- False
--
-- >>> isValue (const 0) (force_ $ force_ $ Builtin FstPair)
-- True
--
isValue
    :: (Var n -> Int)  -- ^ arity of variables
    -> Raw a n
    -> Bool
isValue _ Var {}      = True
isValue _ Free {}     = True
isValue _ Lam {}      = True
isValue _ Delay {}    = True
isValue _ Constant {} = True
isValue _ Builtin {}  = True
isValue _ Error {}    = False
isValue _ Let {}      = False
isValue varArity t@Force {} = case h of
    Builtin b -> builtinArity b > length args
    Var x     -> varArity x > length args
    _         -> False
  where
    (h, args) = peelApp t
isValue varArity t@App {} = case h of
    Builtin b -> builtinArity b > length args
    Var x     -> varArity x > length args
    _         -> False
  where
    (h, args) = peelApp t

-------------------------------------------------------------------------------
-- Smart constructors
-------------------------------------------------------------------------------

-- | Let smart constructor.
--
-- >>> pp $ let_ "x" "foo" $ let_ "y" "bar" "body"
-- let* x = foo
--      y = bar
-- in body
let_ :: Text -> Raw Text n -> Raw Text n -> Raw Text n
let_ n t s = Let (Name n) t (abstract1 n s)

-- | Function abstraction smart constructor.
--
-- >>> pp $ lam_ "x" $ "x" :@ "x"
-- \ x -> x x
--
lam_ :: Text -> Raw Text n -> Raw Text n
lam_ n t = Lam (Name n) (abstract1 n t)

-- | Function abstraction for multiple arguments.
--
-- >>> pp $ lams_ ["x", "f"] $ "f" :@ "x"
-- \ x f -> f x
--
lams_ :: [Text] -> Raw Text n -> Raw Text n
lams_ n t = foldr lam_ t n

-- | Infix version of 'App'
--
-- >>> pp $ lam_ "x" $ "x" :@ "x"
-- \ x -> x x
--
pattern (:@) :: Raw n a -> Raw n a -> Raw n a
pattern (:@) f x = App f x
infixl 9 :@

-- | N-ary application.
--
-- >>> pp $ apps_ "f" ["x", "y", "z"]
-- f x y z
--
apps_ :: Raw n a -> [Raw n a] -> Raw n a
apps_ = foldl' App

-- | 'Force'.
force_ :: Raw n a -> Raw n a
force_ = Force

-- | 'Delay'.
delay_ :: Raw n a -> Raw n a
delay_ = Delay

ite_ :: Raw n a -> Raw n a -> Raw n a -> Raw n a
ite_ p x y = Force (Builtin IfThenElse) :@ p :@ x :@ y

trace_ :: Raw n a
trace_ = Builtin Trace

str_ :: Text -> Raw n a
str_ t = Constant (mkConstant t)

tt_ :: Raw n a
tt_ = Constant (mkConstant ())

-------------------------------------------------------------------------------
-- Peeling
-------------------------------------------------------------------------------

data Arg a n
    = ArgTerm (Raw a n)
    | ArgForce
    | ArgFun (Raw a n)
  deriving Show

peelApp
    :: Raw a n
    -> (Raw a n, [Arg a n])
peelApp = fmap ($ []) . go where
    go (App f x) = case go f of
        ~(f', xs) -> (f', xs . (ArgTerm x :))
    go (Force t) = case go t of
        ~(f', xs) -> (f', xs . (ArgForce :))
    go t         = (t, id)

appArgs_ :: Raw a n -> [Arg a n] -> Raw a n
appArgs_ = foldl' f where
    f t (ArgTerm s) = t :@ s
    f t (ArgFun s)  = s :@ t
    f t ArgForce    = force_ t

weakenArg :: Arg a n -> Arg a (S n)
weakenArg = mapArgTerm weaken

mapArgTerm :: (Raw a n -> Raw b m) -> Arg a n -> Arg b m
mapArgTerm f (ArgTerm t) = ArgTerm (f t)
mapArgTerm _ ArgForce    = ArgForce
mapArgTerm f (ArgFun t)  = ArgFun (f t)

traverseArgTerm :: Applicative f => (Raw a n -> f (Raw b m)) -> Arg a n -> f (Arg b m)
traverseArgTerm f (ArgTerm t) = ArgTerm <$> f t
traverseArgTerm _ ArgForce    = pure ArgForce
traverseArgTerm f (ArgFun t)  = ArgFun <$> f t
