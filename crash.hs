{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, TypeFamilies #-}

data T a b where
  T1 :: Int -> T Int
  T2 :: (Int -> Int) -> T Moo

class C a where
  op :: T a

instance C Int where
  op = T1 2

newtype Moo = Moo Int
  deriving C

type family F a :: *
type instance F Int = Int
type instance F Moo = Int -> Int

foo :: T a -> F a
foo (T1 n) = n
foo (T2 f) = f

main = print (foo (op :: T Moo) 3)