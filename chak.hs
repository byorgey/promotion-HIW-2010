{-# LANGUAGE GeneralizedNewtypeDeriving, GADTs #-}

class IsInt t where
  isInt :: c Int -> c t

instance IsInt Int where isInt = id

newtype Moo = Moo Int deriving (IsInt, Show)

data Z a where
  ZI :: Double -> Z Int
  ZM :: (Int,Int) -> Z Moo

foo :: Z Moo -> Moo
foo (ZM (i, _)) = Moo i

