module FAT32

import Data.Vect
import Data.Vect.Elem
import Data.So

mutual
    data UniqVect : Nat -> (a : Type) -> Eq a => Type where
        Nil : Eq a => 
              UniqVect 0 a
        (::) : Eq a => 
               (x : a) -> 
               (xs : UniqVect n a) -> 
               (ua : UniqAll (/= x) xs) => 
               UniqVect (S n) a

    data UniqAll : Eq a => (a -> Bool) -> UniqVect n a -> Type where
        Nil' : {0 p : a -> Bool} -> 
               Eq a => 
               UniqAll p Nil
        Cons' : {0 a : Type} ->
                Eq a =>
                {0 p : a -> Bool} ->
                {0 x : a} ->
                {0 xs : UniqVect n a} -> 
                (ua : UniqAll (/= x) xs) => 
                So (p x) -> 
                UniqAll p xs -> 
                UniqAll p (x::xs)

-- namespace Alt
--     %hide FAT32.UniqVect
--     %hide FAT32.UniqAll
--     mutual
--         data UniqVect : Nat -> (a : Type) -> Type where
--             Nil : Eq a => 
--                   UniqVect 0 a
--             (::) : Eq a => 
--                    (x : a) -> 
--                    (xs : UniqVect n a) -> 
--                    UniqAll (/= x) xs => 
--                    UniqVect (S n) a
--
--         data UniqAll : (a -> Bool) -> UniqVect n a -> Type where
--             Nil' : {0 p : a -> Bool} -> 
--                    Eq a => 
--                    UniqAll p Nil
--             Cons' : {0 p : a -> Bool} -> 
--                     So (p x) -> 
--                     UniqAll p xs -> 
--                     UniqAll p ((::) x xs @{peq} @{pall})
--
-- %unhide FAT32.UniqVect
-- %unhide FAT32.UniqAll

data UniqElem : {0 a : Type} -> Eq a => a -> UniqVect n a -> Type where
    Here : {0 a : Type} -> Eq a => {0 x : a} -> {0 xs : UniqVect n a} -> UniqAll (/= x) xs => UniqElem x (x::xs)
    There : {0 a : Type} -> Eq a => {0 y : a} -> {0 x : a} -> {0 xs : UniqVect n a} -> UniqAll (/= y) xs => UniqElem x xs -> UniqElem x ((::) y xs)

(<++>) : Eq a => 
         (xs : UniqVect n a) ->
         (ys : UniqVect m a) -> 
         (uf : {0 x : a} -> 
         UniqElem x xs -> 
         UniqAll (/= x) ys) => 
         UniqVect (n + m) a

prf_x_uniq : {0 a : Type} -> 
             Eq a => 
             (x0 : a) -> 
             (xs' : UniqVect n a) -> 
             (ux : UniqAll (/= x0) xs') -> 
             (ys : UniqVect m a) -> 
             (uf : {0 x : a} -> (UniqElem x ((::) x0 xs') -> UniqAll (/= x) ys)) -> 
             UniqAll (/= x0) ((<++>) xs' ys {uf = \arg => uf (There arg)})

prf_x_uniq x0 [] ux ys uf = ?prf_x_uniq_rhs_0
-- prf_x_uniq x0 ((::) x xs {ua = ux}) (Cons' y z) ys uf = (Cons' y ?Cons'_arg_1 {ua = ?uaaa})
prf_x_uniq x0 ((::) x xs {ua = ux}) (Cons' y z) ys uf = ?rhs1

(<++>) [] ys = ys
(<++>) ((::) x0 xs' {ua = ux}) ys = (::) x0 ((<++>) xs' ys {uf = \arg => uf (There arg)}) {ua = prf_x_uniq x0 xs' ux ys uf}

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
