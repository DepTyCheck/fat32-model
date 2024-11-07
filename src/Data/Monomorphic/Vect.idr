module Data.Monomorphic.Vect

import public Data.Nat
import public Data.FinInc
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

namespace VectFinInc
    public export
    data VectFinInc : Nat -> Nat -> Type where
        Nil : VectFinInc 0 n
        (::) : FinInc n -> VectFinInc k n -> VectFinInc (S k) n

namespace HVectFinInc
    public export
    data HVectFinInc : (k : Nat) -> VectNat k -> Type where
        Nil : HVectFinInc 0 []
        (::) : FinInc n -> HVectFinInc k ns -> HVectFinInc (S k) (n :: ns)
    
    public export
    sum : {ns : VectNat k} -> HVectFinInc k ns -> FinInc (sum ns)
    sum [] = MkFinInc 0 LTEZero
    sum (x :: xs) = x + sum xs

%language ElabReflection
%runElab deriveIndexed "VectNat" [Show]
%runElab deriveIndexed "VectBits8" [Show]
%runElab deriveIndexed "VectFinInc" [Show]
%runElab deriveIndexed "HVectFinInc" [Show]
