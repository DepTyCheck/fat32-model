module Data.Monomorphic.Vect

import public Data.Nat
import Derive.Prelude

%default total

namespace VectNat
    public export
    data VectNat : Nat -> Type where
        Nil : VectNat 0
        (::) : Nat -> VectNat n -> VectNat (S n)

    public export
    sum : VectNat k -> Nat
    sum [] = 0
    sum (x :: xs) = x + sum xs

namespace VectBits8
    public export
    data VectBits8 : Nat -> Type where
        Nil : VectBits8 0
        (::) : Bits8 -> VectBits8 n -> VectBits8 (S n)

    public export
    fromVect : Vect n Bits8 -> VectBits8 n
    fromVect [] = []
    fromVect (x :: xs) = x :: fromVect xs

    public export
    (++) : VectBits8 n -> VectBits8 m -> VectBits8 (n + m)
    [] ++ ys = ys
    (x :: xs) ++ ys = x :: (xs ++ ys)

%language ElabReflection
%runElab deriveIndexed "VectNat" [Show]
%runElab deriveIndexed "VectBits8" [Show]
