module Data.FinInc

import Data.Nat
import Data.Nat.Order.Properties
import Decidable.Decidable
import Decidable.Equality

%default total

public export
data FinInc : Nat -> Type where
    FZ : FinInc k
    FS : FinInc k -> FinInc (S k)

public export
finIncToNat : FinInc n -> Nat
finIncToNat FZ = 0
finIncToNat (FS x) = S (finIncToNat x)

public export
weakenN : (0 n : Nat) -> FinInc m -> FinInc (m + n)
weakenN n FZ = FZ
weakenN n (FS f) = FS (weakenN n f)

public export
(+) : {n, m : Nat} -> FinInc n -> FinInc m -> FinInc (n + m)
(+) FZ y = rewrite plusCommutative n m in weakenN n y
(+) (FS x) y = FS (x + y)

public export
(*) : {n : Nat} -> (a : Nat) -> (b : FinInc n) -> FinInc (a * n)
(*) 0 _ = FZ
(*) (S k) b = b + k * b

public export
divCeilFlip : (b : Nat) -> (0 _ : NonZero b) => (a : FinInc (n * b)) -> FinInc n
divCeilFlip b a = ?rhs

public export
divCeilNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> Nat
divCeilNZ x y p = case (modNatNZ x y p) of
  Z   => divNatNZ x y p
  S _ => S (divNatNZ x y p)

dividentZeroEqZero : (0 y : Nat) -> (0 p : NonZero y) -> divNatNZ 0 y p = 0
dividentZeroEqZero (S _) SIsNonZero = Refl

lteZeroOnlyZero : LTE a 0 -> a = 0
lteZeroOnlyZero LTEZero = Refl

multCommutLTERhs : LTE a (b * n) -> LTE a (n * b)
multCommutLTERhs x = rewrite multCommutative n b in x

divNatNZBounds : (a : Nat) -> (b : Nat) -> (n : Nat) -> (nz : NonZero b) -> LT a (b * n) -> LT (divNatNZ a b nz) n


divCeilNZBounds : (a : Nat) -> (b : Nat) -> (n : Nat) -> (nz : NonZero b) -> LTE a (b * n) -> LTE (Data.FinInc.divCeilNZ a b nz) n
divCeilNZBounds a b n nz ltep with (decomposeLte a (b * n) ltep)
  divCeilNZBounds a b n nz ltep | (Left x) with (modNatNZ a b nz)
    divCeilNZBounds a b n nz ltep | (Left x) | 0 = lteSuccLeft (divNatNZBounds a b n nz x)
    divCeilNZBounds a b n nz ltep | (Left x) | (S _) = divNatNZBounds a b n nz x
  divCeilNZBounds a b n nz ltep | (Right x) = rewrite x in ?divCeilNZBounds_rhs_rhss_1

