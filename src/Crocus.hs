{-# LANGUAGE GADTs #-}
module Crocus
( module Crocus
) where

x = Letrec (\ _ -> choice
  [ fact ["doug", "ayman"]
  , fact ["doug", "beka"]
  , fact ["doug", "max"]
  , fact ["doug", "patrick"]
  , fact ["doug", "rob"]
  , fact ["doug", "rick"]
  , fact ["doug", "tim"]

  , fact ["pavel", "doug"]

  , fact ["rachel", "pavel"]

  , fact ["keith", "rachel"]
  ])
  (\ report ->
  Query $ E $ \ x -> report :$ K "rachel" :$ x)

-- -- rule "coworker" $ \ _X ->


data Decl where
  Letrec :: (Expr -> Expr) -> (Expr -> Decl) -> Decl
  Query :: Expr -> Decl

data Expr where
  (:|) :: Expr -> Expr -> Expr
  (:*) :: Expr -> Expr -> Expr
  (:~) :: Expr -> Expr -> Expr
  (:$) :: Expr -> Expr -> Expr
  K :: String -> Expr
  B :: (Expr -> Expr) -> Expr
  E :: (Expr -> Expr) -> Expr

infixr 5 :|
infixr 6 :*
infixr 7 :~
infixl 9 :$


y = Letrec (\ _ -> choice
  [ fact ["Alice", "Bob"]
  , fact ["Bob", "Charlie"]
  , fact ["Charlie", "Daphne"]
  ])
  $ \ parent ->
  Letrec (\ ancestor -> choice
    [ bind $ \ a b -> parent :$ a :$ b
    , bind $ \ a b -> E $ \ z -> parent :$ a :$ z :* ancestor :$ z :$ b
    ])
  $ \ ancestor ->
  Query $ E $ \ x -> ancestor :$ K "Alice" :$ x

fact :: [String] -> Expr
fact []     = error "fact applied to empty list"
fact [a]    = B $ \ v -> v :~ K a
fact (a:as) = B $ \ v -> v :~ K a :* fact as

choice :: [Expr] -> Expr
choice = foldr1 (:|)

class Bind a where
  bind :: a -> Expr

instance Bind a => Bind (Expr -> a) where
  bind f = B $ bind . f

instance Bind Expr where
  bind = id
