module Data.FinInc

import Data.Nat
import Data.Nat.Division
import Data.Nat.Order
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
natToFinIncLTE : (x : Nat) -> (0 prf : LTE x n) => FinInc n
natToFinIncLTE 0 = FZ
natToFinIncLTE (S k) {prf = (LTESucc x)} = FS (natToFinIncLTE k)

public export
elemLTEBound : (n : FinInc m) -> LTE (finIncToNat n) m
elemLTEBound FZ = LTEZero
elemLTEBound (FS x) = LTESucc (elemLTEBound x)

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
divCeilNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> Nat
divCeilNZ x y p = case (modNatNZ x y p) of
  Z   => divNatNZ x y p
  S _ => S (divNatNZ x y p)

public export
divModMult : (n : Nat) -> (b : Nat) -> (0 nz : NonZero b) -> (divNatNZ (n * b) b nz = n, modNatNZ (n * b) b nz = 0)
divModMult _ 0 SIsNonZero impossible
divModMult n (S k) SIsNonZero = DivisionTheoremUniqueness (n * (S k)) (S k) SIsNonZero n 0 ltZero (sym (plusZeroRightNeutral (n * (S k))))

public export
divMultIsNumer : (n : Nat) -> (b : Nat) -> (0 nz : NonZero b) -> divNatNZ (n * b) b nz = n
divMultIsNumer n b nz = fst (divModMult n b nz)

public export
modMultIsZero : (n : Nat) -> (b : Nat) -> (0 nz : NonZero b) -> modNatNZ (n * b) b nz = 0
modMultIsZero n b nz = snd (divModMult n b nz)

public export
plusLeftLTCancel : (a : Nat) -> (b : Nat) -> (r : Nat) -> LT (r + a) (r + b) -> LT a b
plusLeftLTCancel a b 0 ltr = ltr
plusLeftLTCancel a b (S k) ltr = plusLeftLTCancel a b k (fromLteSucc ltr)

public export
multRightLTCancel : (a : Nat) -> (b : Nat) -> (r : Nat) -> (0 _ : NonZero r) -> LT (a * r) (b * r) -> LT a b
multRightLTCancel 0 0 (S x) SIsNonZero ltr = ltr
multRightLTCancel (S k) 0 (S x) SIsNonZero ltr = void (zeroNeverGreater ltr)
multRightLTCancel 0 (S k) (S x) SIsNonZero ltr = LTESucc LTEZero
multRightLTCancel (S j) (S k) r@(S x) SIsNonZero ltr = LTESucc (multRightLTCancel j k r SIsNonZero (plusLeftLTCancel (j * r) (k * r) r ltr))

public export
divNatNZBounds : (a : Nat) -> (b : Nat) -> (n : Nat) -> (nz : NonZero b) -> LT a (n * b) -> LT (divNatNZ a b nz) n
divNatNZBounds a b@(S b') n SIsNonZero plt = multRightLTCancel (divNatNZ a b SIsNonZero) n b SIsNonZero (transitive plt2 plt1)
  where plt1 : LT (modNatNZ a b SIsNonZero + (divNatNZ a b SIsNonZero * b)) (n * b)
        plt1 = rewrite sym (DivisionTheorem a b SIsNonZero SIsNonZero) in plt
        plt2 : LTE (S (divNatNZ a b SIsNonZero * b)) (S (modNatNZ a b SIsNonZero + (divNatNZ a b SIsNonZero * b)))
        plt2 = LTESucc (rewrite plusCommutative (modNatNZ a b SIsNonZero) (divNatNZ a b SIsNonZero * b) in lteAddRight (divNatNZ a b SIsNonZero * b))

public export
divCeilNZBounds : (a : Nat) -> (b : Nat) -> (n : Nat) -> (nz : NonZero b) -> LTE a (n * b) -> LTE (Data.FinInc.divCeilNZ a b nz) n
divCeilNZBounds a b n nz ltep with (decomposeLte a (n * b) ltep)
  divCeilNZBounds a b n nz ltep | (Left x) with (modNatNZ a b nz)
    divCeilNZBounds a b n nz ltep | (Left x) | 0 = lteSuccLeft (divNatNZBounds a b n nz x)
    divCeilNZBounds a b n nz ltep | (Left x) | (S _) = divNatNZBounds a b n nz x
  divCeilNZBounds a b n nz ltep | (Right x) = 
    rewrite x in
    rewrite (modMultIsZero n b nz) in
    rewrite (divMultIsNumer n b nz) in reflexive

public export
divCeilFlipWeak : {0 n : Nat} -> {0 r : Nat} -> (b : Nat) -> (0 _ : NonZero b) => (a : FinInc (minus (n * b) r)) -> FinInc n
divCeilFlipWeak b @{nz} a = natToFinIncLTE (Data.FinInc.divCeilNZ (finIncToNat a) b nz) @{divCeilNZBounds (finIncToNat a) b n nz (transitive (elemLTEBound a) (minusLTE r (n * b)))}

public export
divCeilFlip : (b : Nat) -> (0 _ : NonZero b) => (a : FinInc (n * b)) -> FinInc n
divCeilFlip b @{nz} a = divCeilFlipWeak b @{nz} (rewrite minusZeroRight (n * b) in a) {r = 0}

