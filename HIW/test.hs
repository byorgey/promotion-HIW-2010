{-# LANGUAGE EmptyDataDecls, TypeFamilies, KindSignatures #-}

data Z
data S n

type family Plus (m::*) (n::*) :: *
type instance Plus Z     n = n
type instance Plus (S m) n = S (Plus m n)
