module FAT32

import Data.Vect
import Data.Vect.Elem
import Data.So

mutual
    data UniqVect : Nat -> (a : Type) -> Type where
        Nil : Eq a => 
              UniqVect 0 a
        (::) : Eq a => 
               (x : a) -> 
               (xs : UniqVect n a) -> 
               UniqAll (/= x) xs => 
               UniqVect (S n) a

    data UniqAll : (a -> Bool) -> UniqVect n a -> Type where
        Nil' : {0 p : a -> Bool} -> 
               Eq a => 
               UniqAll p Nil
        Cons' : {0 p : a -> Bool} -> 
                Eq a => 
                UniqAll (/= x) xs => 
                So (p x) -> 
                UniqAll p xs -> 
                UniqAll p (x::xs)

namespace Alt
    %hide FAT32.UniqVect
    %hide FAT32.UniqAll
    mutual
        data UniqVect : Nat -> (a : Type) -> Type where
            Nil : Eq a => 
                  UniqVect 0 a
            (::) : Eq a => 
                   (x : a) -> 
                   (xs : UniqVect n a) -> 
                   UniqAll (/= x) xs => 
                   UniqVect (S n) a

        data UniqAll : (a -> Bool) -> UniqVect n a -> Type where
            Nil' : {0 p : a -> Bool} -> 
                   Eq a => 
                   UniqAll p Nil
            Cons' : {0 p : a -> Bool} -> 
                    So (p x) -> 
                    UniqAll p xs -> 
                    UniqAll p ((::) x xs @{peq} @{pall})

%unhide FAT32.UniqVect
%unhide FAT32.UniqAll

data UniqElem : a -> UniqVect n a -> Type where
    Here : {0 x : a} -> {0 xs : UniqVect n a} -> Eq a => UniqAll (/= x) xs => UniqElem x (x::xs)
    There : UniqElem x xs -> UniqElem x ((::) @{peq} y xs @{pall})

(<++>) : (conAr : Eq a) => (xs : UniqVect n a) -> (ys : UniqVect m a) -> (uf : {0 x : a} -> UniqElem x xs -> UniqAll (/= x) ys) => UniqVect (n + m) a

prf_x_uniq : {0 a : Type} -> (auto_eq : Eq a) => (x0 : a) -> (xs' : UniqVect n a) -> (ux : UniqAll (\arg => arg /= x0) xs') -> (ys : UniqVect m a) -> (uf : {0 x : a} -> (UniqElem x ((::) @{auto_eq} x0 xs' @{ux}) -> UniqAll (\arg => arg /= x) ys)) -> UniqAll (\arg => arg /= x0) ((<++>) @{auto_eq} xs' ys @{?uhh})
prf_x_uniq = ?prf_x_uniq_rhs

-- какие-то беды с интансами `Eq a`, peq и conAr потенциально разные инстансы, и оно не тайпчекается (если вместо ?ux подставить ux итд)
(<++>) [] ys = ys
(<++>) ((::) @{peq} x xs' @{ux}) ys = (::) @{conAr} x ((<++>) @{conAr} xs' ys @{?new_uf}) @{prf_x_uniq @{conAr} x xs' ?ux ys ?uf}

(++) : (n ** Vect n a) -> (m ** Vect m a) -> (p ** Vect p a)
(n ** xs) ++ (m ** ys) = ((n + m) ** (xs ++ ys))

concat : Vect k (n ** Vect n a) -> (p ** Vect p a)
concat = foldr (++) (0 ** [])

data Metadata : Type where

ClusterSize : Nat
ClusterSize = 512

DirentSize : Nat
DirentSize = 32

data Node : Vect n Nat -> Vect m Nat -> Type

GetClusterList : Maybe (n ** cl : Vect n Nat ** m ** tl : Vect m Nat ** Node cl tl) -> (m ** Vect m Nat)
GetClusterList Nothing = (0 ** Nil)
GetClusterList (Just x) = (_ ** (fst $ snd $ snd $ snd x))

data Node : Vect n Nat -> Vect m Nat -> Type where
    File : (meta : Metadata) 
        -> (contents : Vect (n * ClusterSize) Bits8)
        -> Node clusterList totalList
    Dir : (meta : Metadata)
        -> (entries : Vect k (Maybe (n ** cl : Vect n Nat ** m ** tl : Vect m Nat ** Node cl tl)))
        -> {0 clusterList : Vect (divCeil (k * DirentSize) ClusterSize) Nat}
        -> Node clusterList (clusterList ++ snd (concat (map GetClusterList entries)))
