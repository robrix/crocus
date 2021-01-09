{-# LANGUAGE GADTs #-}
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

type RelName = String

type Entity = String

data EntityExpr
  = K Entity
  | V Var

newtype Var = Var { getVar :: Int }
  deriving (Enum, Eq, Num, Ord)

instance Show Var where
  showsPrec _ (Var i) = upper i
    where
    upper = toAlpha ['A'..'Z']

toAlpha :: String -> Int -> ShowS
toAlpha alphabet i = (alphabet !! r :) . if q > 0 then shows q else id
  where
  n = length alphabet
  (q, r) = i `divMod` n

incr :: Var -> Var
incr = succ


newtype Expr = Disj { disj :: NonEmpty Conj }

newtype Conj = Conj { conj :: [Pattern] }
  deriving (Monoid, Semigroup)

data Pattern = Pattern RelName [EntityExpr]


(\/), (/\) :: Expr -> Expr -> Expr
Disj e1 \/ Disj e2 = Disj (e1 <> e2)
Disj e1 /\ Disj e2 = Disj $ (<>) <$> e1 <*> e2

infixr 6 \/
infixr 7 /\

rel :: RelName -> [EntityExpr] -> Expr
rel n e = Disj $ Conj [Pattern n e]:|[]



type Env = [Entry]
data Entry = Entry { var :: Var, val :: Entity }

instance Show Entry where
  showsPrec d (Entry var val) = showParen (d > 0) $ shows var . showString " : " . shows val


data Fact = Fact RelName [Entity]
  deriving (Eq, Ord, Show)

data Rel = Rel RelName Q

data Q
  = ForAll (Var -> Q)
  | Expr Expr

runVar :: ReaderC Var m a -> m a
runVar = runReader (Var 0)

bind :: Has (Reader Var) sig m => (Var -> m a) -> m a
bind f = do
  v <- ask
  local incr (f v)


unbind :: Has (Reader Var) sig m => Q -> ([Var] -> Expr -> m a) -> m a
unbind q k = go [] q
  where
  go accum = \case
    ForAll f -> bind $ \ v -> go (v:accum) (f v)
    Expr e   -> k (reverse accum) e


evalStep :: (Alternative m, Has (Reader Var) sig m) => m Rel -> m Fact -> m Fact -> m Fact
evalStep rels facts delta = do
  Rel n q <- rels
  unbind q $ \ params body -> do
    u <- matchExpr facts delta body
    pure $ Fact n (map (substVar u) params)

eval :: (Alternative m, Foldable m, Algebra sig m) => m Rel -> m Fact -> m Fact
eval rels facts = go empty facts
  where
  go facts delta =
    let facts' = facts <|> delta
        delta' = runVar (evalStep (lift rels) (lift facts) (lift delta)) in
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
  [ defRel "org" $ \ _A _B -> rel "report" [V _A, V _B] \/ rel "report" [V _A, V 2] /\ rel "org" [V 2, V _B]
  ]

class Relation r where
  rhs :: r -> Q

instance Relation Expr where
  rhs = Expr

instance Relation r => Relation (Var -> r) where
  rhs f = ForAll (rhs . f)

defRel :: Relation r => RelName -> r -> Rel
defRel n b = Rel n (rhs b)


substVar :: Env -> Var -> Entity
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
matchDisj delta = matchConj delta <=< oneOfBalanced . disj


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

-- data Decl where
--   Letrec :: (Expr -> Expr) -> (Expr -> Decl) -> Decl
--   Query :: Expr -> Decl

-- data Expr where
--   (:|) :: Expr -> Expr -> Expr
--   (:*) :: Expr -> Expr -> Expr
--   (:~) :: Expr -> Expr -> Expr
--   (:$) :: Expr -> Expr -> Expr
--   K :: String -> Expr
--   B :: (Expr -> Expr) -> Expr
--   E :: (Expr -> Expr) -> Expr

-- infixr 5 :|
-- infixr 6 :*
-- infixr 7 :~
-- infixl 9 :$


-- x = Letrec (\ _ -> choice
--   [ fact ["doug", "ayman"]
--   , fact ["doug", "beka"]
--   , fact ["doug", "max"]
--   , fact ["doug", "patrick"]
--   , fact ["doug", "rob"]
--   , fact ["doug", "rick"]
--   , fact ["doug", "tim"]

--   , fact ["pavel", "doug"]

--   , fact ["rachel", "pavel"]

--   , fact ["keith", "rachel"]
--   ])
--   (\ report ->
--   Query $ E $ \ x -> report :$ K "rachel" :$ x)

-- y = Letrec (\ _ -> choice
--   [ fact ["Alice", "Bob"]
--   , fact ["Bob", "Charlie"]
--   , fact ["Charlie", "Daphne"]
--   ])
--   $ \ parent ->
--   Letrec (\ ancestor -> choice
--     [ bind $ \ a b -> parent :$ a :$ b
--     , bind $ \ a b -> E $ \ z -> parent :$ a :$ z :* ancestor :$ z :$ b
--     ])
--   $ \ ancestor ->
--   Query $ E $ \ x -> ancestor :$ K "Alice" :$ x

-- fact :: [String] -> Expr
-- fact []     = error "fact applied to empty list"
-- fact [a]    = B $ \ v -> v :~ K a
-- fact (a:as) = B $ \ v -> v :~ K a :* fact as

-- choice :: [Expr] -> Expr
-- choice = foldr1 (:|)

-- class Bind a where
--   bind :: a -> Expr

-- instance Bind a => Bind (Expr -> a) where
--   bind f = B $ bind . f

-- instance Bind Expr where
--   bind = id


-- q1 = Query $ K "a"
-- v1 = ["a"]
