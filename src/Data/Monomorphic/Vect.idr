module Data.Monomorphic.Vect

import public Data.Nat
import Derive.Prelude
import Deriving.DepTyCheck.Gen
import public Data.ByteVect

%default total

-- namespace VectNat
--     public export
--     data VectNat : Nat -> Type where
--         Nil : VectNat 0
--         (::) : Nat -> VectNat n -> VectNat (S n)
--
--     public export
--     sum : VectNat k -> Nat
--     sum [] = 0
--     sum (x :: xs) = x + sum xs

public export %hint
genBits8 : Gen MaybeEmpty Bits8
genBits8 = elements' $ the (List Bits8) [0..255]

public export
packVect : {n : Nat} -> Vect n Bits8 -> ByteVect n
packVect xs = BV (buffer xs) 0 reflexive

namespace VectBits8
    public export
    data VectBits8 : Nat -> Type where
        Nil : VectBits8 0
        (::) : Bits8 -> VectBits8 n -> VectBits8 (S n)

    public export
    record VectBits8Pair n m where
        constructor MkVectBits8Pair
        fst : VectBits8 n
        snd : VectBits8 m

    public export
    fromVect : Vect n Bits8 -> VectBits8 n
    fromVect [] = []
    fromVect (x :: xs) = x :: fromVect xs
    
    public export
    toVect : VectBits8 n -> Vect n Bits8
    toVect [] = []
    toVect (x :: xs) = x :: toVect xs

    public export
    (++) : VectBits8 n -> VectBits8 m -> VectBits8 (n + m)
    [] ++ ys = ys
    (x :: xs) ++ ys = x :: (xs ++ ys)

    public export
    splitAt : (n : Nat) -> (xs : VectBits8 (n + m)) -> VectBits8Pair n m
    splitAt 0 xs = MkVectBits8Pair [] xs
    splitAt (S k) (x :: xs) with (splitAt k xs)
      splitAt (S k) (x :: xs) | (MkVectBits8Pair fst snd) = MkVectBits8Pair (x :: fst) snd
    
    public export
    Eq (VectBits8 k) where
        (==) [] [] = True
        (==) (x :: xs) (y :: ys) = (x == y) && (xs == ys)
    
    public export
    genVectBits8 : (n : Nat) -> Gen MaybeEmpty (VectBits8 n)
    genVectBits8 0 = pure []
    genVectBits8 (S k) = [| genBits8 :: genVectBits8 k |]

    public export
    packVect : {n : Nat} -> VectBits8 n -> ByteVect n
    packVect = packVect . toVect


%language ElabReflection
-- %runElab deriveIndexed "VectNat" [Show]
%runElab deriveIndexed "VectBits8" [Show]
