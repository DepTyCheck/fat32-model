module Data.Fin.Div

import Data.Fin
import Data.Fin.Arith

%default total

data PosFin : (n : Nat) -> Fin n -> Type where
    SIsPositive : PosFin (S n) (FS x)

-- divCeil : {n : Nat} -> (a : Fin (S n)) -> (b : Fin m) -> PosFin m b => Fin (S n)
-- divCeil FZ _ = FZ
-- divCeil {n = 0} (FS y) b impossible
-- divCeil {n = (S _)} a@(FS y) b = case isLT (finToNat a) (finToNat b) of
--                                     (Yes prf) => FS FZ
--                                     (No contra) => ?divCeil_rhs_3
-- func : Fin (S n) -> Fin (S n)
-- func FZ = FZ
-- func (FS x) = FS FZ

divCeil : (a : Fin (S n)) -> (b : Nat) -> Fin n 

