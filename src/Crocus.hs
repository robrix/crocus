module Crocus
( module Crocus
) where

import Control.Carrier.NonDet.Church
import Data.Functor.Identity

type Relation = String

type Constant = String

-- type Variable = String

fact :: Relation -> [Constant] -> Program ()
fact _ _ = Program (pure ())

-- rule :: Relation -> [Either Variable Constant] -> Program ()

-- query ::


newtype Program a = Program (NonDetC Identity a)
  deriving (Applicative, Functor, Monad)

x = do
  fact "report" ["doug", "ayman"]
  fact "report" ["doug", "beka"]
  fact "report" ["doug", "max"]
  fact "report" ["doug", "patrick"]
  fact "report" ["doug", "rob"]
  fact "report" ["doug", "rick"]
  fact "report" ["doug", "tim"]

  fact "report" ["pavel", "doug"]

  fact "report" ["rachel", "pavel"]

  fact "report" ["keith", "rachel"]

-- -- rule "coworker" $ \ _X ->


data Decl =
  Let Relation Expr

data Expr
  = Expr :|: Expr
  | Expr :*: Expr
  | Expr :~: Expr
  | K Constant
  | B (Expr -> Expr)

infixr 5 :|:
infixr 6 :*:
infixr 7 :~:


parent = Let "parent" $ choice
  [ fact' ["Alice", "Bob"]
  , fact' ["Bob", "Charlie"]
  , fact' ["Charlie", "Daphne"]
  ]

fact' :: [Constant] -> Expr
fact' []     = error "fact' applied to empty list"
fact' [a]    = B $ \ v -> v :~: K a
fact' (a:as) = B $ \ v -> v :~: K a :*: fact' as

choice :: [Expr] -> Expr
choice = foldr1 (:|:)
