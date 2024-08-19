module Data.Disjoint

import Data.Nat
import Data.List
import Data.Vect
import Data.Vect.Quantifiers
import Decidable.Decidable
import Decidable.Equality

%default total


data NotEq : a -> a -> Type where
    MkNotEq : {x : t} -> 
              {y : t} -> 
              Not (x = y) -> 
              NotEq x y

fromFalse : (d : Dec p) -> (isFalse : isYes d = False) => Not p
fromFalse (Yes prf) {isFalse = Refl} impossible
fromFalse (No contra) = contra

%hint
notEq : DecEq t => {x : t} -> {y : t} -> (isFalse : isYes (decEq x y) = False) => NotEq x y
notEq = MkNotEq (fromFalse (decEq _ _))

namespace Uniq
    public export
    data Uniq : Vect n a -> Type where
        Nil : Uniq []
        (::) : All (\y => NotEq y x) xs -> 
               Uniq xs -> 
               Uniq (x :: xs)

namespace Disjoint
    public export
    data Disjoint : Vect n a -> Vect m a -> Type where
        Nil : Disjoint [] ys
        (::) : All (\y => NotEq y x) ys -> 
               Disjoint xs ys -> 
               Disjoint (x :: xs) ys

VecVec : Vect k Nat -> Type -> Type
VecVec shape t = All (flip Vect t) shape

namespace AllAll
    public export
    data AllAll : {0 xs : Vect n a} -> 
                  {0 p : (a -> Type)} -> 
                  (0 p2 : {0 x : a} -> (p x -> Type)) -> 
                  All p xs -> 
                  Type where
        Nil : {0 p : (a -> Type)} -> 
              {0 p2 : {0 x : a} -> (p x -> Type)} -> 
              AllAll p2 []
        (::) : {0 p : (a -> Type)} -> 
               {0 p2 : {0 x : a} -> (p x -> Type)} -> 
               {0 x0 : a} -> 
               {0 v : p x0} -> 
               {0 vs : All p xs} -> 
               p2 v -> 
               AllAll p2 vs -> 
               AllAll p2 (v :: vs)

-- namespace DisjointUnion
--     public export
--     data DisjointUnion : Vect k (n ** Vect n a) -> Type where
--         Nil : DisjointUnion Nil
--         (::) : {0 x : (m ** Vect m a)} -> 
--                {0 xs : Vect k (m ** Vect m a)} -> 
--                All (\y => Disjoint y (snd x)) (map Builtin.DPair.DPair.snd xs) -> 
--                DisjointUnion (x :: xs)

namespace DisjointUnion
    public export
    data DisjointUnion : VecVec shape a -> Type where
        Nil : DisjointUnion Nil
        (::) : {0 x : Vect n a} -> {0 xs : VecVec shape a} -> AllAll (\y => Disjoint y x) xs -> DisjointUnion xs -> DisjointUnion (x :: xs)

sum : Vect n Nat -> Nat
sum [] = 0
sum (x :: xs) = x + sum xs


allAppend : All p xs -> All p ys -> All p (xs ++ ys)
allAppend [] y = y
allAppend (x :: z) y = x :: allAppend z y

allConcat : VecVec shape a -> Vect (sum shape) a 
allConcat [] = []
allConcat (x :: xs) = x ++ (allConcat xs)

disjointAppendIsUniq : Uniq xs -> Uniq ys -> Disjoint xs ys -> Uniq (xs ++ ys)
disjointAppendIsUniq [] uy [] = uy
disjointAppendIsUniq (ux :: uxs) uy (dj :: djs) = (allAppend ux dj) :: (disjointAppendIsUniq uxs uy djs)


disjointConcatIsUniq : {0 xs : VecVec shape a} -> AllAll Uniq xs {p = flip Vect a} -> DisjointUnion xs -> Uniq (allConcat xs)
disjointConcatIsUniq [] y = ?disjointConcatIsUniq_rhs_0
disjointConcatIsUniq (x :: z) y = ?disjointConcatIsUniq_rhs_1

