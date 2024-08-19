module FAT32

import Data.Vect
import Data.Vect.Elem
import Data.So

mutual
    data UniqVect : Nat -> (a : Type) -> Eq a => Type where
        Nil : Eq a => UniqVect 0 a
        (::) : Eq a => (x : a) -> (xs : UniqVect n a) -> All (/= x) xs => UniqVect (S n) a

    data All : Eq a => (a -> Bool) -> UniqVect n a -> Type where
        Nil' : Eq a => All @{peq} p (Nil @{peq})
        Cons' : {p : a -> Bool} -> So (p x) -> All @{peq} p xs -> All @{peq} p ((::) x xs @{peq} @{pall})



data Metadata : Type where

ClusterSize : Nat
ClusterSize = 512

DirentSize : Nat
DirentSize = 32

data Node : Vect n Nat -> Vect m Nat -> Type

GetClusterList : Maybe (n ** cl : Vect n Nat ** m ** tl : Vect m Nat ** Node cl tl) -> (n ** Vect n Nat)
GetClusterList Nothing = (0 ** Nil)
GetClusterList (Just x) = (_ ** (fst $ snd $ snd $ snd x))

data Node : Vect n Nat -> Vect m Nat -> Type where
    File : (meta : Metadata) 
        -> (contents : Vect (n * ClusterSize) Bits8)
        -> Node clusterList totalList
    Dir : (meta : Metadata)
        -> (entries : Vect k (Maybe (n ** cl : Vect n Nat ** m ** tl : Vect m Nat ** Node cl tl)))
        -> {0 clusterList : Vect (divCeil (k * DirentSize) ClusterSize) Nat}
        -> Node clusterList (clusterList ++ concat (map (snd . GetClusterList) entries))
