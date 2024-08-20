module Data.Fin.Weakening

import Data.Fin

%default total

divCeil : Fin n -> Fin m -> Fin n
divCeil FZ _ = FZ
divCeil (FS x) y = ?divCeil_rhs_1

