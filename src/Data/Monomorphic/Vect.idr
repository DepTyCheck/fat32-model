module Data.Monomorphic.Vect

import public Data.Nat
import Derive.Prelude
import Deriving.DepTyCheck.Gen
import public Data.Buffer.Core
import public Data.Buffer.Indexed

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
    replicate : (n : Nat) -> Bits8 -> VectBits8 n
    replicate 0 m = []
    replicate (S k) m = m :: replicate k m

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
    packVect : {n : Nat} -> VectBits8 n -> IBuffer n
    packVect = buffer . toVect

namespace SnocVectBits8
    public export
    data SnocVectBits8 : Nat -> Type where
        Lin : SnocVectBits8 0
        (:<) : (SnocVectBits8 n) -> Bits8 -> SnocVectBits8 (S n)

    public export
    Eq (SnocVectBits8 k) where
        (==) [<] [<]             = True
        (==) (sx :< x) (sy :< y) = (x == y) && (sx == sy)

    public export
    (++) : SnocVectBits8 n -> SnocVectBits8 m -> SnocVectBits8 (n + m)
    sx ++ [<] = rewrite plusZeroRightNeutral n in sx
    sx ++ ((:<) sy y {n=m'}) =
        rewrite sym $ plusSuccRightSucc n m' in
            (sx ++ sy) :< y

    public export
    (<><) : SnocVectBits8 n -> VectBits8 m -> SnocVectBits8 (n + m)
    sx <>< [] = rewrite plusZeroRightNeutral n in sx
    sx <>< ((::) x xs {n=m'}) =
        rewrite sym $ plusSuccRightSucc n m' in
            sx :< x <>< xs

    -- public export
    -- (<>>) : SnocVectBits8 n -> VectBits8 m -> VectBits8 (n + m)
    -- Lin       <>> xs = xs
    -- ((:<) sx x {n=n'}) <>> xs =
    --     rewrite plusSuccRightSucc n' m in
    --       sx <>> x :: xs
    
    public export
    (<>>) : SnocVectBits8 n -> Vect m Bits8 -> Vect (n + m) Bits8
    Lin       <>> xs = xs
    ((:<) sx x {n=n'}) <>> xs =
        rewrite plusSuccRightSucc n' m in
          sx <>> x :: xs
    
    public export
    packVect : {n : Nat} -> SnocVectBits8 n -> IBuffer n
    packVect sx = rewrite sym $ plusZeroRightNeutral n in buffer $ sx <>> []
    
    public export
    genSnocVectBits8 : (n : Nat) -> Gen MaybeEmpty (SnocVectBits8 n)
    genSnocVectBits8 0 = pure [<]
    genSnocVectBits8 (S k) = [| genSnocVectBits8 k :< genBits8 |]

%language ElabReflection
-- %runElab deriveIndexed "VectNat" [Show]
%runElab deriveIndexed "VectBits8" [Show]
%runElab deriveIndexed "SnocVectBits8" [Show]
