module Data.UniqFinVect

import Deriving.DepTyCheck.Gen
import Data.Array.Core
import Data.Array.Indexed

public export
data UniqFinVect : (k : Nat) -> (n : Nat) -> Type

public export
data NotIn : Fin n -> UniqFinVect k n -> Type

data UniqFinVect : (k : Nat) -> (n : Nat) -> Type where
  Nil  : UniqFinVect Z n
  (::) : (s : Fin n) -> (ss : UniqFinVect k n) -> NotIn s ss => UniqFinVect (S k) n

data NotIn : Fin n -> UniqFinVect k n -> Type where
  N : NotIn x []
  S : {0 x : Fin n} -> {0 s : Fin n} -> {0 sub : NotIn s ss} -> So (x /= s) => NotIn x ss -> NotIn x $ (s::ss) @{sub}

public export
genUniqFinVect : Fuel -> (k : Nat) -> (n : Nat) -> Gen MaybeEmpty $ UniqFinVect k n

public export
toVect : UniqFinVect k n -> Vect k (Fin n)
toVect [] = []
toVect (s::ss) = s :: toVect ss

public export
toArray : {k : Nat} -> UniqFinVect k n -> IArray k (Fin n)
toArray = array . toVect

