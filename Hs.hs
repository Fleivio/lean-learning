{-# LANGUAGE UndecidableInstances #-}
module Hs() where

import Data.Void

excludedMiddle :: Either a (a -> Void)
excludedMiddle = undefined

class MyMonad t where
    myBind :: t a -> (a -> t b) -> t b 
    myPure :: a -> t a

class MyFunctor t where
    myMap :: (a -> b) -> t a -> t b

instance MyMonad t => MyFunctor t where
    myMap f t = myBind t (myMap f . myPure)