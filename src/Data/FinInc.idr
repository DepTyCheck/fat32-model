module Data.FinInc

import public Data.Nat
import public Data.Nat.Division
import public Data.Nat.Order
import public Data.Nat.Order.Properties
import public Decidable.Decidable
import public Decidable.Equality
import public Syntax.PreorderReasoning
import Derive.Prelude

%default total

public export
record FinInc n where
    constructor MkFinInc
    val : Nat
    prf : LTE val n

public export
(+) : {n, m : Nat} -> FinInc n -> FinInc m -> FinInc (n + m)
(+) (MkFinInc vx px) (MkFinInc vy py) = MkFinInc (vx + vy) (plusLteMonotone px py)

public export
(*) : {n : Nat} -> (a : Nat) -> (b : FinInc n) -> FinInc (a * n)
(*) a (MkFinInc val prf) = MkFinInc (a * val) (multLteMonotoneRight a val n prf)

-- public export
-- divCeilNZ : Nat -> (y: Nat) -> (0 _ : NonZero y) -> Nat
-- divCeilNZ x y p = case (modNatNZ x y p) of
--   Z   => divNatNZ x y p
--   S _ => S (divNatNZ x y p)

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
divNatNZBounds : (a : Nat) -> (b : Nat) -> (n : Nat) -> (0 nz : NonZero b) -> LT a (n * b) -> LT (divNatNZ a b nz) n
divNatNZBounds a b@(S b') n SIsNonZero plt = multRightLTCancel (divNatNZ a b SIsNonZero) n b SIsNonZero (transitive plt2 plt1)
  where plt1 : LT (modNatNZ a b SIsNonZero + (divNatNZ a b SIsNonZero * b)) (n * b)
        plt1 = rewrite sym (DivisionTheorem a b SIsNonZero SIsNonZero) in plt
        plt2 : LTE (S (divNatNZ a b SIsNonZero * b)) (S (modNatNZ a b SIsNonZero + (divNatNZ a b SIsNonZero * b)))
        plt2 = LTESucc (rewrite plusCommutative (modNatNZ a b SIsNonZero) (divNatNZ a b SIsNonZero * b) in lteAddRight (divNatNZ a b SIsNonZero * b))

public export
divCeilNZBounds : (a : Nat) -> (b : Nat) -> (n : Nat) -> (0 nz : NonZero b) -> LTE a (n * b) -> LTE (divCeilNZ a b nz) n
divCeilNZBounds a b n nz ltep with (decomposeLte a (n * b) ltep)
  divCeilNZBounds a b n nz ltep | (Left x) with (modNatNZ a b nz)
    divCeilNZBounds a b n nz ltep | (Left x) | 0 = lteSuccLeft (divNatNZBounds a b n nz x)
    divCeilNZBounds a b n nz ltep | (Left x) | (S _) = divNatNZBounds a b n nz x
  divCeilNZBounds a b n nz ltep | (Right x) = 
    rewrite x in
    rewrite (modMultIsZero n b nz) in
    rewrite (divMultIsNumer n b nz) in reflexive

public export
numerMinusModIsDenomMultQuot : (0 a : Nat) -> (0 b : Nat) -> (0 nz : NonZero b) => minus a (modNatNZ a b nz) = b * divNatNZ a b nz
numerMinusModIsDenomMultQuot a b = Calc $
    |~ (a `minus` modNatNZ a b nz)
    ~~ (modNatNZ a b nz + divNatNZ a b nz * b `minus` modNatNZ a b nz) ...(cong (`minus` modNatNZ a b nz) $ DivisionTheorem a b nz nz)
    ~~ (divNatNZ a b nz * b) ...(minusPlus $ modNatNZ a b nz)
    ~~ (b * divNatNZ a b nz) ...(multCommutative (divNatNZ a b nz) b)

public export
divCeilFlipWeak : {n : Nat} -> {r : Nat} -> (b : Nat) -> (0 _ : NonZero b) => (a : FinInc (minus (n * b) r)) -> FinInc n
divCeilFlipWeak b @{nz} (MkFinInc va pa) = MkFinInc (divCeilNZ va b nz) (divCeilNZBounds va b n nz (transitive pa (minusLTE r (n * b))))

-- public export
-- divCeilFlip : {n : Nat} -> (b : Nat) -> (0 _ : NonZero b) => (a : FinInc (n * b)) -> FinInc n
-- divCeilFlip b @{nz} a = divCeilFlipWeak b @{nz} (rewrite minusZeroRight (n * b) in a) {r = 0}

public export
divCeilFlip : {n : Nat} -> (b : Nat) -> (0 _ : NonZero b) => (a : FinInc (n * b)) -> FinInc n
divCeilFlip b @{nz} (MkFinInc va pa) = MkFinInc (divCeilNZ va b nz) (divCeilNZBounds va b n nz pa)

%language ElabReflection
%runElab deriveIndexed "LTE" [Show]
%runElab deriveIndexed "FinInc" [Show]
