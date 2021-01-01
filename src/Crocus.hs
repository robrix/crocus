module Crocus
() where

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

-- -- rule "coworker" $ \ _X ->
