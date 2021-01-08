{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Crocus
( module Crocus
) where

import Control.Carrier.NonDet.Church
import Control.Monad ((<=<))
import Data.Foldable (toList)
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromJust)

type VarName = String

type RelName = String

type Entity = String

data EntityExpr
  = K Entity
  | V VarName

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



type Env = [(VarName, Entity)]


data Fact = Fact RelName [Entity]
  deriving (Eq, Ord, Show)

data Rel = Rel RelName [VarName] Expr


evalStep :: [Rel] -> [Fact] -> [Fact] -> [Fact]
evalStep rels facts delta = do
  Rel n params body <- rels
  u <- matchExpr facts delta body
  pure $ Fact n (map (substVar u) params)

eval :: [Rel] -> [Fact] -> [Fact]
eval rels facts = go [] facts
  where
  go facts delta =
    let facts' = nub $ facts <> delta
        delta' = evalStep rels facts delta in
    if all (`elem` facts') delta' then
      facts'
    else
      go facts' delta'


query :: [Rel] -> [Fact] -> Expr -> [Env]
query rels facts = matchDisj derived
  where
  derived = eval rels facts


facts :: Alternative m => m Fact
facts = oneOf
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
rels = oneOf
  [ Rel "org" ["A", "B"] (rel "report" [V "A", V "B"] \/ rel "report" [V "A", V "Z"] /\ rel "org" [V "Z", V "B"])
  ]


substVar :: Env -> VarName -> Entity
substVar e n = fromJust $ lookup n e

subst :: Env -> Expr -> Expr
subst env = Disj . fmap (substConj env) . disj

substConj :: Env -> Conj -> Conj
substConj env = Conj . fmap (substPattern env) . conj

substPattern :: Env -> Pattern -> Pattern
substPattern env (Pattern n e) = Pattern n (map go e)
  where
  go = \case
    K a -> K a
    V n -> maybe (V n) K (lookup n env)

matchExpr :: [Fact] -> [Fact] -> Expr -> [Env]
matchExpr facts delta expr = nub $ do
  (u, conj') <- matchDisj1 delta expr
  u' <- matchConj (facts ++ delta) (substConj u conj')
  pure $ u <> u'


quotient :: [a] -> [(a, [a])]
quotient []     = []
quotient (x:xs) = go [] x xs where
  go accum x = \case
    []     -> [(x, reverse accum)]
    x':xs' -> (x, reverse accum ++ x' : xs') : go (x : accum) x' xs'

quotient' :: MSplit m => m a -> m (a, m a)
quotient' m = do
  r <- msplit m
  case r of
    Nothing      -> empty
    Just (a, as) -> go [] a as where
      go accum a as = do
        r <- msplit as
        case r of
          Nothing        -> pure (a, oneOf (reverse accum))
          Just (a', as') -> pure (a, oneOf (reverse accum) <|> pure a' <|> as') <|> go (a:accum) a' as'


matchDisj1 :: [Fact] -> Expr -> [(Env, Conj)]
matchDisj1 delta = matchConj1 delta <=< toList . disj

matchDisj :: (Alternative m, Monad m) => m Fact -> Expr -> m Env
matchDisj delta = matchConj delta <=< oneOf . disj


matchConj1 :: MSplit m => m Fact -> Conj -> m (Env, Conj)
matchConj1 delta (Conj conj) = do
  (p, rest) <- quotient' (oneOf conj)
  u <- matchPattern delta p
  rest' <- runL rest
  pure (u, Conj rest')

matchConj :: (Alternative m, Monad m) => m Fact -> Conj -> m Env
matchConj facts = go . conj where
  go = \case
    []  -> pure []
    h:t -> do
      uh <- matchPattern facts h
      ut <- matchConj facts (substConj uh (Conj t))
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
    (V v:as, a':as') -> ((v, a') :) <$> go as as'
    (_, _)           -> Nothing


class (Alternative m, Monad m) => MSplit m where
  msplit :: m a -> m (Maybe (a, m a))

  interleave :: m a -> m a -> m a
  interleave a b = do
    r <- msplit a
    case r of
      Nothing       -> b
      Just (r', a') -> pure r' <|> interleave b a'

  (>>-) :: m a -> (a -> m b) -> m b
  a >>- k = do
    r <- msplit a
    case r of
      Nothing       -> empty
      Just (r', a') -> interleave (k r') (a' >>- k)

  infixr 1 >>-

  ifte :: m a -> (a -> m b) -> m b -> m b
  ifte c t e = do
    r <- msplit c
    case r of
      Nothing       -> e
      Just (r', c') -> t r' <|> (c' >>= t)

  once :: m a -> m a
  once a = do
    r <- msplit a
    case r of
      Nothing      -> empty
      Just (r', _) -> pure r'

instance MSplit Maybe where
  msplit = Just . maybe Nothing (\ a -> Just (a, Nothing))

instance MSplit [] where
  msplit = \case
    []  -> [Nothing]
    h:t -> [Just (h, t)]

runL :: MSplit m => m a -> m [a]
runL m = do
  r <- msplit m
  case r of
    Nothing      -> pure []
    Just (a, m') -> (a:) <$> runL m'


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
