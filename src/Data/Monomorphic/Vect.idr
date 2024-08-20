module Data.Monomorphic.Vect

import Data.Fin

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

namespace VectFin
    public export
    data VectFin : Nat -> Nat -> Type where
        Nil : VectFin 0 n
        (::) : Fin n -> VectFin k n -> VectFin (S k) n
