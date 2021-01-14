{-# LANGUAGE DataKinds #-}
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
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.Maybe (fromJust)
import           Data.Word

type RelName = String

type Entity = String

data EntityExpr
  = K Entity
  | V (Var Entity)

data Var a
  = U Word32
  | X Word32
  deriving (Eq, Ord)

instance Show (Var a) where
  showsPrec _ = upper . fromIntegral . \case
    U i -> i
    X i -> i
    where
    upper = toAlpha ['A'..'Z']

toAlpha :: String -> Int -> ShowS
toAlpha alphabet i = (alphabet !! r :) . if q > 0 then shows q else id
  where
  n = length alphabet
  (q, r) = i `divMod` n

incr :: Var a -> Var a
incr = \case
  U i -> U (i + 1)
  X i -> X (i + 1)


newtype Expr = Disj { disj :: NonEmpty Conj }

newtype Conj = Conj { conj :: [Pattern] }
  deriving (Monoid, Semigroup)

data Pattern = Pattern RelName [EntityExpr]


(\/) :: Expr -> Expr -> Expr
Disj e1 \/ Disj e2 = Disj (e1 <> e2)
(/\) :: Expr -> Expr -> Expr
Disj e1 /\ Disj e2 = Disj $ (<>) <$> e1 <*> e2

infixr 6 \/
infixr 7 /\

rel :: RelName -> [EntityExpr] -> Expr
rel n e = Disj $ Conj [Pattern n e]:|[]


type Env = [Entry]
data Entry = Entry { var :: Var Entity, val :: Entity }

instance Show Entry where
  showsPrec d (Entry var val) = showParen (d > 0) $ shows var . showString " : " . shows val


data Fact = Fact RelName [Entity]
  deriving (Eq, Ord, Show)

data Rel = Rel RelName [Var Entity] Expr

data Row f ts where
  RNil :: Row f '[]
  (:.) :: f t -> Row f ts -> Row f (t ': ts)

infixr 5 :.


evalStep :: (Alternative m, Monad m) => m Rel -> m Fact -> m Fact -> m Fact
evalStep rels facts delta = do
  Rel n params body <- rels
  u <- matchExpr facts delta body
  pure $ Fact n (map (substVar u) params)

eval :: (Alternative m, Foldable m, Monad m) => m Rel -> m Fact -> m Fact
eval rels facts = go empty facts
  where
  go facts delta =
    let facts' = facts <|> delta
        delta' = evalStep rels facts delta in
    if null delta' then
      facts'
    else
      go facts' delta'


query :: (Alternative m, Foldable m, Algebra sig m) => m Rel -> m Fact -> Expr -> m Env
query rels facts = matchDisj derived
  where
  derived = eval rels facts


facts :: Alternative m => m Fact
facts = oneOfBalanced
  [ Fact "report" ["doug", "ayman"]
  , Fact "report" ["doug", "beka"]
  , Fact "report" ["doug", "max"]
  , Fact "report" ["doug", "patrick"]
  , Fact "report" ["doug", "rob"]
  , Fact "report" ["doug", "rick"]
  , Fact "report" ["doug", "tim"]

  , Fact "report" ["pavel", "doug"]

  , Fact "report" ["rachel", "pavel"]

  , Fact "report" ["keith", "rachel"]
  ]

rels :: Alternative m => m Rel
rels = oneOfBalanced
  [ defRel "org" $ \ _A _B
    -> rel "report" [_A, _B]
    \/ exists (\ _Z -> rel "report" [_A, _Z] /\ rel "org" [_Z, _B])
  , defRel "teammate" $ \ _A _B
    -> exists (\ _Z -> rel "report" [_Z, _A] /\ rel "report" [_Z, _B])
  ]


defRel :: Relation r => RelName -> r -> Rel
defRel n = uncurry (Rel n) . rhs (U 0) []

class Relation r where
  rhs :: Var Entity -> [Var Entity] -> r -> ([Var Entity], Expr)

instance Relation Expr where
  rhs _ vs = (reverse vs,)

instance Relation r => Relation (EntityExpr -> r) where
  rhs v vs f = rhs (incr v) (v:vs) (f (V v))


exists :: (EntityExpr -> Expr) -> Expr
exists = snd . rhs (X 0) []


substVar :: Env -> Var Entity -> Entity
substVar e n = val . fromJust $ find ((== n) . var) e

subst :: Env -> Expr -> Expr
subst env = Disj . fmap (substConj env) . disj

substConj :: Env -> Conj -> Conj
substConj env = Conj . fmap (substPattern env) . conj

substPattern :: Env -> Pattern -> Pattern
substPattern env (Pattern n e) = Pattern n (map go e)
  where
  go = \case
    K a -> K a
    V n -> maybe (V n) (K . val) (find ((== n) . var) env)

matchExpr :: (Alternative m, Monad m) => m Fact -> m Fact -> Expr -> m Env
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


matchDisj1 :: (Alternative m, Monad m) => m Fact -> Expr -> m (Env, Conj)
matchDisj1 delta = matchConj1 delta <=< oneOfBalanced . disj

matchDisj :: (Alternative m, Monad m) => m Fact -> Expr -> m Env
matchDisj facts = matchConj facts <=< oneOfBalanced . disj


matchConj1 :: (Alternative m, Monad m) => m Fact -> Conj -> m (Env, Conj)
matchConj1 delta (Conj conj) = do
  (p, rest) <- oneOfBalanced $ quotient conj
  u <- matchPattern delta p
  pure (u, Conj rest)

matchConj :: (Alternative m, Monad m) => m Fact -> Conj -> m Env
matchConj facts = go where
  go = \case
    Conj []  -> pure []
    Conj (h:t) -> do
      uh <- matchPattern facts h
      ut <- go (substConj uh (Conj t))
      pure $ uh <> ut

matchPattern :: (Alternative m, Monad m) => m Fact -> Pattern -> m Env
matchPattern facts (Pattern n e) = do
  Fact n' e' <- facts
  guard (n == n')
  maybe empty pure (go e e')
  where
  go :: [EntityExpr] -> [Entity] -> Maybe Env
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
