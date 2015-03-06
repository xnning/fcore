module Main where

import Test.Tasty
import Test.Tasty.HUnit

-- import tests
import TypeSystem

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [typeSystem]
