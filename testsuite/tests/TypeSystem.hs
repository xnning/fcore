{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module TypeSystem where

import Test.Tasty
import Test.Tasty.HUnit

import Src

import Data.Data

typeSystem = testGroup "Type system" [substitution, subtyping, intersection]

substitution = testGroup "substitution"
  [ testGroup "doesn't replace bound variables" $
      flip map [Forall, OpLam] $ \f ->
        testCase (show (toConstr (f undefined undefined))) $
          subst ("X", y) (f ["X"] x) @?= f ["X"] x

  , testGroup "doesn't make free variables become bound" $
      flip map [Forall, OpLam] $ \f ->
        testCase (show (toConstr (f undefined undefined))) $
          subst ("X", z) (f ["Z"] x) @?= f ["Z"] x

  , testCase "[X -> Y Z](\\Y. X Y) = (\\Y. X Y)" $
      subst ("X", OpApp y [z]) (OpLam ["Y"] (OpApp x [y])) @?= OpLam ["Y"] (OpApp x [y])
  ]

subtyping = testGroup "subtyping" [reflexive]

reflexive = testGroup "reflexive"
  [ testCase "A <: A" $
     a `subtype` a @?= True

  , testCase "A -> A <: A -> A" $
     (a `Fun` a) `subtype` (a `Fun` a) @?= True

  , testCase "forall A. A -> A <: forall A. A -> A" $
      Forall ["A"] (a `Fun` a) `subtype` Forall ["A"] (a `Fun` a) @?= True

  , testCase "forall A. A -> A <: forall B. B -> B" $
      Forall ["A"] (a `Fun` a) `subtype` Forall ["B"] (b `Fun` b) @?= True
  ]

intersection = testGroup "intersection" [commutative, idempotent, assocative]

commutative = testGroup "commutative (A ∧ B = B ∧ A)"
  [ testCase "Int & Float = Float & Int" $
      (javaInt `And` javaFloat) `compatible` (javaFloat `And` javaInt) @?= True
  ]

idempotent  = testGroup "idempotent (A ∧ A = A)"
  [ testCase "Int & Int = Int" $
      (javaInt `And` javaInt) `compatible` javaInt @?= True
  ]

assocative = testGroup "associative ((A ∧ B) ∧ C = A ∧ (B ∧ C))"
  [ testCase "(A & B) & C = A & (B & C)" $
      ((a `And` b) `And` c) `compatible` (a `And` (b `And` c)) @?= True
  ]


-- Utilities
a = TVar "A"
b = TVar "B"
c = TVar "C"
x = TVar "X"
y = TVar "Y"
z = TVar "Z"
