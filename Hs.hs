module Hs() where

import Data.Void

excludedMiddle :: Either a (a -> Void)
excludedMiddle = undefined
