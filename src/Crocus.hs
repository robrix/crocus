{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Crocus
( module Crocus
) where

import Control.Carrier.NonDet.Church
import Data.List (nub)
import Data.Maybe (fromJust)
-- import qualified Data.Map as Map

type VarName = String

type RelName = String

type Entity = String

data EntityExpr
  = K Entity
  | V VarName

data Expr
  = T
  | Rel RelName [EntityExpr]
  | Expr :\/ Expr
  | Expr :/\ Expr

infixr 6 :\/
infixr 7 :/\


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

data RelDef = RelDef [VarName] Expr


evalStep :: [(RelName, RelDef)] -> [Fact] -> [Fact]
evalStep rels facts = do
  (n, RelDef params body) <- rels
  u <- matchExpr facts body
  pure $ Fact n (map (substVar u) params)

eval :: [(RelName, RelDef)] -> [Fact] -> [Fact]
eval rels facts =
  let facts' = evalStep rels facts in
  if all (`elem` facts) facts' then
    facts
  else
    eval rels (nub (facts <> facts'))


query :: [(RelName, RelDef)] -> [Fact] -> Expr -> [Env]
query rels facts = matchExpr derived
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

rels :: Alternative m => m (RelName, RelDef)
rels = oneOf
  [ ("org", RelDef ["A", "B"] (Rel "report" [V "A", V "B"] :\/ Rel "report" [V "A", V "Z"] :/\ Rel "org" [V "Z", V "B"]))
  ]


substVar :: Env -> VarName -> Entity
substVar e n = fromJust $ lookup n e

subst :: Env -> Expr -> Expr
subst env = \case
  T       -> T
  l :\/ r -> subst env l :\/ subst env r
  l :/\ r -> subst env l :\/ subst env r
  Rel n e -> Rel n (map go e)
    where
    go = \case
      K a -> K a
      V n -> maybe (V n) K (lookup n env)

matchExpr :: [Fact] -> Expr -> [Env]
matchExpr facts = \case
  T       -> [[]]
  l :\/ r -> nub (matchExpr facts l <> matchExpr facts r)
  l :/\ r -> nub $ do
    ul <- matchExpr facts l
    ur <- matchExpr facts (subst ul r)
    pure $ ul <> ur
  Rel n e -> matchRel facts n e
  -- pattern match against db; look up n and match/produce substitution of es

matchRel :: [Fact] -> RelName -> [EntityExpr] -> [Env]
matchRel facts n e = do
  Fact n' e' <- facts
  guard (n == n')
  maybe [] pure (go e e')
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
