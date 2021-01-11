{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Crocus
( module Crocus
) where

import qualified Control.Algebra as Alg
import           Control.Carrier.NonDet.Church
import           Control.Carrier.Reader
import           Control.Monad ((<=<))
import           Control.Monad.Trans.Class
import           Data.Foldable (find, toList)
import           Data.Functor.Identity
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe (fromJust)
import           Data.Word

type RelName = String

data Entity
  = S String
  | I Int
  deriving (Eq, Ord, Show)

data EntityExpr a
  = K Entity
  | V a

newtype Var = Var { getVar :: Word32 }
  deriving (Bounded, Enum, Eq, Num, Ord)

instance Show Var where
  showsPrec _ (Var i) = upper (fromIntegral i)
    where
    upper = toAlpha ['A'..'Z']

toAlpha :: String -> Int -> ShowS
toAlpha alphabet i = (alphabet !! r :) . if q > 0 then shows q else id
  where
  n = length alphabet
  (q, r) = i `divMod` n

incr :: Var -> Var
incr = succ


newtype Expr a = Disj { disj :: NonEmpty (Conj a) }

data Exists a
  = Exists (a -> Exists a)
  | Body (Conj a)

instance Semigroup (Exists a) where
  Body a   <> Body b   = Body (a <> b)
  Exists f <> Exists g = Exists (\ v -> f v <> g v)
  Exists f <> b        = Exists (\ v -> f v <> b)
  a        <> Exists g = Exists (\ v -> a   <> g v)

newtype Conj a = Conj { conj :: [Pattern a] }
  deriving (Monoid, Semigroup)

data Pattern a = Pattern RelName [EntityExpr a]


(\/) :: Expr a -> Expr a -> Expr a
Disj e1 \/ Disj e2 = Disj (e1 <> e2)
(/\) :: Expr a -> Expr a -> Expr a
Disj e1 /\ Disj e2 = Disj $ (<>) <$> e1 <*> e2

infixr 6 \/
infixr 7 /\


class Pat a v | a -> v where
  rel :: RelName -> [EntityExpr v] -> a

instance Pat (Pattern a) a where
  rel = Pattern

instance Pat (Conj a) a where
  rel n e = Conj [rel n e]

instance Pat (Expr a) a where
  rel n e = Disj $ rel n e:|[]

exists :: (EntityExpr a -> Exists a) -> Exists a
exists f = Exists (f . V)


type Env a = [Entry a]
data Entry a = Entry { var :: a, val :: Entity }

instance Show a => Show (Entry a) where
  showsPrec d (Entry var val) = showParen (d > 0) $ shows var . showString " : " . shows val


data Fact = Fact RelName [Entity]
  deriving (Eq, Ord, Show)

data Rel a = Rel RelName (Q a)

newtype Closed f = Closed { open :: forall x . f x }

data Q a
  = ForAll (a -> Q a)
  | Expr (Expr a)


unbind :: Has (Scope var) sig m => Q var -> ([var] -> Expr var -> m a) -> m a
unbind q k = go [] q
  where
  go accum = \case
    ForAll f -> bind $ \ v -> go (v:accum) (f v)
    Expr e   -> k (reverse accum) e


evalStep :: (Alternative m, Eq var, Has (Scope var) sig m) => m (Rel var) -> m Fact -> m Fact -> m Fact
evalStep rels facts delta = do
  Rel n q <- rels
  unbind q $ \ params body -> do
    u <- matchExpr facts delta body
    pure $ Fact n (map (substVar u) params)

eval :: forall var m sig . (Alternative m, Enum var, Eq var, Foldable m, Algebra sig m) => m (Rel var) -> m Fact -> m Fact
eval rels facts = go empty facts
  where
  go facts delta =
    let facts' = facts <|> delta
        delta' = runScope (toEnum 0 :: var) (evalStep (lift rels) (lift facts) (lift delta)) in
    if null delta' then
      facts'
    else
      go facts' delta'


query :: (Enum var, Eq var, Alternative m, Foldable m, Algebra sig m) => m (Rel var) -> m Fact -> Expr var -> m (Env var)
query rels facts = matchDisj derived
  where
  derived = eval rels facts


facts :: Alternative m => m Fact
facts = oneOfBalanced
  [ Fact "report" [S "doug", S "ayman"]
  , Fact "report" [S "doug", S "beka"]
  , Fact "report" [S "doug", S "max"]
  , Fact "report" [S "doug", S "patrick"]
  , Fact "report" [S "doug", S "rob"]
  , Fact "report" [S "doug", S "rick"]
  , Fact "report" [S "doug", S "tim"]

  , Fact "report" [S "pavel", S "doug"]

  , Fact "report" [S "rachel", S "pavel"]

  , Fact "report" [S "keith", S "rachel"]
  ]

rels :: Has (Scope Var) sig m => m (Rel Var)
rels = pure
  $ defRel "org" $ \ _A _B -> rel "report" [_A, _B] \/ rel "report" [_A, V 2] /\ rel "org" [V 2, _B]


class Relation r v | r -> v where
  rhs :: Has (Scope v) sig m => r -> m (Expr v)

instance Relation (Expr v) v where
  rhs = pure

instance Relation r v => Relation (EntityExpr v -> r) v where
  rhs f = bind (rhs . f . V)

defRel :: forall v r . (Enum v, Bounded v, Relation r v) => RelName -> r -> Rel v
defRel n b = Rel n $ Expr $ run (runScope (minBound :: v) (rhs b))


substVar :: Eq a => Env a -> a -> Entity
substVar e n = val . fromJust $ find ((== n) . var) e

subst :: Eq a => Env a -> Expr a -> Expr a
subst env = Disj . fmap (substConj env) . disj

substExists :: Eq a => Env a -> Exists a -> Exists a
substExists env = \case
  Body c   -> Body (substConj env c)
  Exists f -> Exists (substExists env . f)

substConj :: Eq a => Env a -> Conj a -> Conj a
substConj env = Conj . fmap (substPattern env) . conj

substPattern :: Eq a => Env a -> Pattern a -> Pattern a
substPattern env (Pattern n e) = Pattern n (map go e)
  where
  go = \case
    K a -> K a
    V n -> maybe (V n) (K . val) (find ((== n) . var) env)

matchExpr :: (Alternative m, Eq a, Monad m) => m Fact -> m Fact -> Expr a -> m (Env a)
matchExpr facts delta expr = do
  (u, conj') <- matchDisj1 delta expr
  u' <- matchConj (facts <|> delta) (substConj u conj')
  pure $ u <> u'


quotient :: [a] -> [(a, [a])]
quotient []     = []
quotient (x:xs) = go [] x xs where
  go accum x = \case
    []     -> [(x, reverse accum)]
    x':xs' -> (x, reverse accum ++ x' : xs') : go (x : accum) x' xs'


matchDisj1 :: (Alternative m, Monad m) => m Fact -> Expr a -> m (Env a, Conj a)
matchDisj1 delta = matchConj1 delta <=< oneOfBalanced . disj

matchDisj :: (Alternative m, Eq a, Monad m) => m Fact -> Expr a -> m (Env a)
matchDisj facts = matchConj facts <=< oneOfBalanced . disj


matchExists1 :: (Alternative m, Has (Scope a) sig m) => m Fact -> Exists a -> m (Env a, Exists a)
matchExists1 delta = go where
  go = \case
    Body c   -> fmap Body <$> matchConj1 delta c
    Exists f -> bind (go . f) -- FIXME: this needs to reconstruct the binder!

matchExists :: (Alternative m, Eq a, Has (Scope a) sig m) => m Fact -> Exists a -> m (Env a)
matchExists facts = go where
  go = \case
    Body c   -> matchConj facts c
    Exists f -> bind (go . f)


matchConj1 :: (Alternative m, Monad m) => m Fact -> Conj a -> m (Env a, Conj a)
matchConj1 delta (Conj conj) = do
  (p, rest) <- oneOfBalanced $ quotient conj
  u <- matchPattern delta p
  pure (u, Conj rest)

matchConj :: (Alternative m, Eq a, Monad m) => m Fact -> Conj a -> m (Env a)
matchConj facts = go where
  go = \case
    Conj []  -> pure []
    Conj (h:t) -> do
      uh <- matchPattern facts h
      ut <- go (substConj uh (Conj t))
      pure $ uh <> ut

matchPattern :: (Alternative m, Monad m) => m Fact -> Pattern a -> m (Env a)
matchPattern facts (Pattern n e) = do
  Fact n' e' <- facts
  guard (n == n')
  maybe empty pure (go e e')
  where
  go :: [EntityExpr a] -> [Entity] -> Maybe (Env a)
  go = curry $ \case
    ([], [])         -> Just []
    (K a:as, a':as') -> guard (a == a') *> go as as'
    (V v:as, a':as') -> (Entry v a' :) <$> go as as'
    (_, _)           -> Nothing


data B a = E | L a | B (B a) (B a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Applicative B where
  pure = L
  E     <*> _ = E
  L f   <*> a = f <$> a
  B l r <*> a = (l <*> a) <|> (r <*> a)

instance Alternative B where
  empty = E
  E <|> r = r
  l <|> E = l
  l <|> r = B l r

instance Monad B where
  E     >>= _ = E
  L a   >>= k = k a
  B l r >>= k = (l >>= k) <|> (r >>= k)

instance Algebra NonDet B where
  alg _ sig ctx = case sig of
    Alg.L Empty  -> E
    Alg.R Choose -> B (L (True <$ ctx)) (L (False <$ ctx))

instance Semigroup (B a) where
  (<>) = B

instance Monoid (B a) where
  mempty = E

oneOfBalanced :: (Alternative m, Foldable t) => t a -> m a
-- FIXME: is there perhaps some clever Monoid we could fold with to do this?
oneOfBalanced as = go (length as) (toList as)
  where
  go n = \case
    []  -> empty
    [a] -> pure a
    as  -> go half (take half as) <|> go (n - half) (drop half as)
      where
      half = n `div` 2


bind :: Has (Scope var) sig m => (var -> m a) -> m a
bind f = Alg.send (Bind f)

data Scope var m a where
  Bind :: (var -> m a) -> Scope var m a


runScope :: var -> ScopeC var m a -> m a
runScope v = runReader v . runScopeC

newtype ScopeC var m a = ScopeC { runScopeC :: ReaderC var m a }
  deriving (Alternative, Applicative, Functor, Monad, MonadTrans)

instance (Enum var, Algebra sig m) => Algebra (Scope var Alg.:+: sig) (ScopeC var m) where
  alg hdl sig ctx = ScopeC $ case sig of
    Alg.L (Bind f) -> do
      v <- ask
      local (succ @var) (runScopeC (hdl (f v <$ ctx)))
    Alg.R other    -> Alg.alg (runScopeC . hdl) (Alg.R other) ctx


runCrocus :: ScopeC Var Identity a -> a
runCrocus = run . runScope minBound


-- x = do
--   parent <- _fact "parent" $ \ parent ->
--     [ parent "Alice" "Beth"
--     , parent "Alice" "Bob"
--     , parent "Andy" "Beth"
--     , parent "Andy" "Bob"
--     ]

--   ancestor <- _rel "ancestor" $ \ ancestor ->
--     \ a b -> parent a b `_disj` _exists (\ z -> parent a z `_conj` ancestor z b)

--   sibling <- _rel "sibling" $ \ sibling ->
--     \ a b -> _exists $ \ p -> parent p a `_conj` parent p b

--   _
