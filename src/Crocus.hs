{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Crocus
( module Crocus
) where

import Control.Carrier.NonDet.Church
import Control.Monad (forM, (<=<))
import Data.Foldable (toList)
import Data.List (nub)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromJust)
-- import qualified Data.Map as Map

type VarName = String

type RelName = String

type Entity = String

data EntityExpr
  = K Entity
  | V VarName

type Expr = NonEmpty Conj

type Conj = [Pattern]

data Pattern = Pattern RelName [EntityExpr]



(\/), (/\) :: Expr -> Expr -> Expr
e1 \/ e2 = e1 <> e2
e1 /\ e2 = (<>) <$> e1 <*> e2

infixr 6 \/
infixr 7 /\

rel :: RelName -> [EntityExpr] -> Expr
rel n e = [Pattern n e]:|[]



type Env = [(VarName, Entity)]

-- (|-) :: Relation Env Expr


-- tarski :: Env -> Expr -> Bool
-- tarski env = \case


-- x :- a
-- x :- b

-- x :- a | b

data Fact = Fact RelName [Entity]
  deriving (Eq, Ord, Show)


-- type Rules = Map.Map RelName RelDef

data Rel = Rel RelName [VarName] Expr


{-

1. match at least one thing against the delta (at least one pattern comes from the delta)
2. union delta with remainder of facts

-}


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
query rels facts = matchConj derived <=< toList
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
subst env = fmap (fmap (substPattern env))

substPattern :: Env -> Pattern -> Pattern
substPattern env (Pattern n e) = Pattern n (map go e)
  where
  go = \case
    K a -> K a
    V n -> maybe (V n) K (lookup n env)

matchExpr :: [Fact] -> [Fact] -> Expr -> [Env]
matchExpr facts delta expr = nub $ do
  (u, conj') <- match1Disj delta expr
  u' <- matchConj (facts ++ delta) (substPattern u <$> conj')
  pure $ u <> u'

-- matchExpr facts = nub . (matchConj facts <=< toList)

quotient :: [a] -> [(a, [a])]
quotient []     = []
quotient (x:xs) = go [] x xs where
  go accum x = \case
    []     -> [(x, reverse accum)]
    x':xs' -> (x, reverse accum ++ x' : xs') : go (x : accum) x' xs'


match1Disj :: [Fact] -> Expr -> [(Env, Conj)]
match1Disj delta = match1Conj delta <=< toList


match1Conj :: [Fact] -> Conj -> [(Env, Conj)]
match1Conj delta conj = do
  (p, rest) <- quotient conj
  u <- matchPattern delta p
  pure (u, rest)

matchConj :: (Alternative m, Monad m) => m Fact -> Conj -> m Env
matchConj facts = go where
  go = \case
    []  -> pure []
    h:t -> do
      uh <- matchPattern facts h
      ut <- matchConj facts (substPattern uh <$> t)
      pure $ uh <> ut
  -- pattern match against db; look up n and match/produce substitution of es

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


  -- l :/\ r -> matchExpr facts (subst (matchExpr facts l) r)


-- eval :: Expr -> [Fact] -> ([Fact] -> [Env]) -> [Env]
-- eval e db k = case e of
--   F -> []


-- P(X, Y) /\ Q(Y, Z)

-- P(1, 2), Q(2, 3)


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


-- ancestor(A, B) :- parent(A, B)
-- ancestor(A, B) :- parent(A, Z), ancestor(Z, B)

-- ancestor :- (\ A B -> parent A B) | (\ A B -> exists $ \ Z -> parent A Z, ancestor(Z, B))

-- ancestor A B :- parent A B | exists …


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
