module Filesystems.FAT32.Utils

import Algebra.Solver.Semiring
import Data.Nat
import Data.DPair
import Data.Nat.Order.Properties
import Data.Nat.Division

%default total
%ambiguity_depth 5

export
0 eqPrf1 : (a, b, c, d : Nat) -> (a + b * (c + d)) + c + d = a + (1 + b) * (c + d)
eqPrf1 a b c d = solveNat [a, b, c, d] 
    ((a .+ b .* (c .+. d)) +. c +. d)
    (a .+ (1 +. b) * (c .+. d))

export
0 eqPrf2 : (a, b, c, d : Nat) -> (c + d) + (a + b * (c + d)) = a + (1 + b) * (c + d)
eqPrf2 a b c d = solveNat [a, b, c, d] 
    ((c .+. d) + (a .+ b .* (c .+. d)))
    (a .+ (1 +. b) * (c .+. d))

export
0 eqPrf3 : (a, b, c, d : Nat) -> (a + b * (c + d)) + (c + d) = a + (1 + b) * (c + d)
eqPrf3 a b c d = solveNat [a, b, c, d] 
    ((a .+ b .* (c .+. d)) + (c .+. d))
    (a .+ (1 +. b) * (c .+. d))

export
0 eqPrf4 : (a, b, c : Nat) -> (a + b * c) + c = a + (1 + b) * c
eqPrf4 a b c = solveNat [a, b, c] 
    ((a .+ b .*. c) +. c)
    (a .+ (1 +. b) *. c)

public export
eqToLTE : {b : Nat} -> a = b -> LTE a b
eqToLTE Refl = reflexive

-- TODO: erase LTE proofs
boundedRange' : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => (fuel : Nat) -> List $ Subset Nat (`LT` b)
boundedRange' a b 0 = []
boundedRange' a b (S k) with (decomposeLte a b prf)
    boundedRange' a b (S k) | (Right peq) = []
    boundedRange' a b (S k) | (Left plt) with (boundedRange' (S a) b k)
      boundedRange' a b (S k) | (Left plt) | ps = (Element a plt) :: ps

public export
boundedRangeLT : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => List $ Subset Nat (`LT` b)
boundedRangeLT a b = boundedRange' a b (minus b a)

public export
boundedRangeLTE : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => List $ Subset Nat (`LTE` b)
boundedRangeLTE a b = map (bimap id fromLteSucc) $ boundedRange' a (S b) (S $ minus b a) @{lteSuccRight prf}

boundedRangeD' : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => (fuel : Nat) -> List (x ** x `LT` b)
boundedRangeD' a b 0 = []
boundedRangeD' a b (S k) with (decomposeLte a b prf)
    boundedRangeD' a b (S k) | (Right peq) = []
    boundedRangeD' a b (S k) | (Left plt) with (boundedRangeD' (S a) b k)
      boundedRangeD' a b (S k) | (Left plt) | ps = (a ** plt) :: ps

public export
boundedRangeDLT : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => List (x ** x `LT` b)
boundedRangeDLT a b = boundedRangeD' a b (minus b a)

public export
boundedRangeDLTE : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => List (x ** x `LTE` b)
boundedRangeDLTE a b = map (bimap id fromLteSucc) $ boundedRangeD' a (S b) (S $ minus b a) @{lteSuccRight prf}

public export
multLteMonotone : {a, b, c, d : Nat} -> LTE a b -> LTE c d -> LTE (a * c) (b * d)
multLteMonotone x y = multLteMonotoneLeft a b c x `transitive` multLteMonotoneRight b c d y

%hide Data.Nat.divCeilNZ

public export
divCeilNZ : Nat -> (y: Nat) -> (0 _ : IsSucc y) => Nat
divCeilNZ x y = case (modNatNZ x y %search) of
    Z   => divNatNZ x y %search
    S _ => S (divNatNZ x y %search)

export
divCeilMultLTE : (a : Nat) -> (b : Nat) -> {0 bnz : IsSucc b} -> LTE a (divCeilNZ a b @{bnz} * b)
divCeilMultLTE a b with (DivisionTheorem a b bnz bnz, boundModNatNZ a b bnz) | (modNatNZ a b bnz)
    divCeilMultLTE a b | (dv, mb) | 0 = rewrite sym dv in reflexive
    divCeilMultLTE a b | (dv, mb) | (S k) = rewrite cong (\x => LTE x $ b + divNatNZ a b bnz * b) dv in plusLteMonotoneRight (divNatNZ a b bnz * b) _ _ $ lteSuccLeft mb

export
multIsSucc : (a : Nat) -> (b : Nat) -> IsSucc (a * b) -> (IsSucc a, IsSucc b)
multIsSucc 0 b prf = void $ uninhabited prf
multIsSucc (S k) 0 prf = void $ uninhabited $ replace {p = IsSucc} (multZeroRightZero k) prf
multIsSucc (S k) (S j) prf = (ItIsSucc, ItIsSucc)

public export
isSuccToLTE : IsSucc a -> LTE 1 a
isSuccToLTE ItIsSucc = LTESucc LTEZero

public export
divCeilIsSucc : (a : Nat) -> (b : Nat) -> {0 bnz : IsSucc b} -> (0 prf : IsSucc a) => LTE 1 (divCeilNZ a b @{bnz})
divCeilIsSucc 0 b = void $ uninhabited prf
divCeilIsSucc (S k) b with (DivisionTheorem (S k) b bnz bnz) | (modNatNZ (S k) b bnz)
  divCeilIsSucc (S k) b | dv | 0 = isSuccToLTE $ fst $ multIsSucc (divNatNZ (S k) b bnz) b (rewrite sym dv in ItIsSucc)
  divCeilIsSucc (S k) b | dv | (S j) = isSuccToLTE ItIsSucc

public export
plusOneRight : (x : Nat) -> S x = x + 1
plusOneRight x = sym (plusOneSucc x) `trans` plusCommutative 1 x

