module Data.Monomorphic.Vect

import Data.Nat
import Data.Nat.Order.Properties
import Derive.Prelude
import Deriving.DepTyCheck.Gen
import Data.Buffer.Core
import Data.Buffer.Indexed

%default total
%language ElabReflection
%prefix_record_projections off

public export
minusLeftSuccLTE : (a : Nat) -> (b : Nat) -> LTE a b -> S (minus b a) = minus (S b) a 
minusLeftSuccLTE 0 0 x = Refl
minusLeftSuccLTE 0 (S k) x = Refl
minusLeftSuccLTE (S k) (S _) (LTESucc x) = minusLeftSuccLTE k _ x

public export
data Presence = Present | Absent
%runElab derive "Presence" [Show, Eq]

namespace SnocVectPresence
    public export
    data SnocVectPresence : Nat -> Type where
        Lin : SnocVectPresence Z
        (:<) : SnocVectPresence k -> Presence -> SnocVectPresence (S k)
    %runElab deriveIndexed "SnocVectPresence" [Show]

public export %hint
genBits8 : Gen MaybeEmpty Bits8
-- genBits8 = elements' $ the (List Bits8) [0..255]
genBits8 = relax chooseAny

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
    drop : (xs : VectBits8 n) -> (m : Nat) -> VectBits8 $ minus n m
    drop [] m = []
    drop (n :: x) 0 = n :: x
    drop (n :: x) (S k) = drop x k
    
    public export
    Eq (VectBits8 k) where
        (==) [] [] = True
        (==) (x :: xs) (y :: ys) = (x == y) && (xs == ys)
    
    public export
    genVectBits8 : (n : Nat) -> Gen MaybeEmpty (VectBits8 n)
    genVectBits8 0 = pure []
    genVectBits8 (S k) = [| genBits8 :: genVectBits8 k |]

    public export
    genBlob : (blobLimit : Nat) -> Gen MaybeEmpty (k ** VectBits8 k)
    genBlob blobLimit = do
      k <- elements' $ the (List Nat) [0..blobLimit]
      blob <- genVectBits8 k
      pure (k ** blob)

    public export
    packVect : {n : Nat} -> VectBits8 n -> IBuffer n
    packVect = buffer . toVect

    toCharList : VectBits8 n -> List Char
    toCharList [] = []
    toCharList (x :: xs) = cast x :: toCharList xs

    public export
    Interpolation (VectBits8 n) where
        interpolate xs = pack $ toCharList xs

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
    replicate : (n : Nat) -> Bits8 -> SnocVectBits8 n
    replicate 0 m = [<]
    replicate (S k) m = replicate k m :< m
    
    public export
    packVect : {n : Nat} -> SnocVectBits8 n -> IBuffer n
    packVect sx = rewrite sym $ plusZeroRightNeutral n in buffer $ sx <>> []
    
    public export
    genSnocVectBits8 : (n : Nat) -> Gen MaybeEmpty (SnocVectBits8 n)
    genSnocVectBits8 0 = pure [<]
    genSnocVectBits8 (S k) = [| genSnocVectBits8 k :< genBits8 |]
    
    public export
    genBlob : (blobLimit : Nat) -> Gen MaybeEmpty (k ** SnocVectBits8 k)
    genBlob blobLimit = do
      k <- elements' $ the (List Nat) [0..blobLimit]
      blob <- genSnocVectBits8 k
      pure (k ** blob)
    
    public export
    ifNotRightThenLeft : Either a b -> Not b -> a
    ifNotRightThenLeft (Left x) f = x
    ifNotRightThenLeft (Right x) f = void $ f x

    public export
    slice : {n : Nat} -> (sx : SnocVectBits8 n) -> (src : Nat) -> (len : Nat) -> (0 lprf : LTE (src + len) n) => SnocVectBits8 len
    slice sx src 0 @{lprf} = [<]
    slice [<] src (S k) @{lprf} = void $ uninhabited $ replace {p = \x => LTE x 0} (sym $ plusSuccRightSucc src k) lprf
    slice {n = n@(S n')} (sx :< x) src (S k) @{lprf} with (decEq (src + S k) n)
      _ | (Yes prf) = slice sx src k @{eqLTE _ _ $ injective {f = S} $ rewrite plusSuccRightSucc src k in prf} :< x
      _ | (No contra) = slice sx src (S k) @{fromLteSucc $ ifNotRightThenLeft (decomposeLte _ _ lprf) contra}

    public export
    truncate : {n : Nat} -> (ssx : SnocVectBits8 n) -> (off : Nat) -> VectBits8 accl -> (SnocVectBits8 off, VectBits8 $ minus n off + accl)
    truncate [<] off acc = (replicate _ 0, acc)
    truncate {n = n@(S n')} ssx@(sx :< x) off acc with (isGTE off n)
      _ | (Yes prf) = (replace {p = SnocVectBits8} (plusCommutative _ _ `trans` plusMinusLte (S n') off prf) $ ssx <>< replicate (minus off $ S n') 0, replace {p = VectBits8} (cong (+ accl) $ (sym $ minusPlusZero (S n') (minus off $ S n')) `trans` cong (minus $ S n') (plusCommutative (S n') (minus off $ S n') `trans` plusMinusLte _ _ prf)) acc)
      _ | (No contra) = replace {p = \px => (SnocVectBits8 off, VectBits8 px)} ((sym $ plusSuccRightSucc (minus n' off) accl) `trans` cong (+ accl) {a = S $ minus n' off} (minusLeftSuccLTE _ _ $ fromLteSucc $ notLTEImpliesGT contra)) $ truncate sx off (x :: acc)

    public export
    overwriteAt : {n : Nat} -> (sx : SnocVectBits8 n) -> (off : Nat) -> {len : Nat} -> (ys : VectBits8 len) -> SnocVectBits8 (off + len + minus (minus n off) len)
    overwriteAt sx off ys with (truncate sx off [])
      _ | (sv, vs) = rewrite sym $ plusZeroRightNeutral $ minus n off in sv <>< ys <>< drop vs len

%runElab deriveIndexed "VectBits8" [Show]
%runElab deriveIndexed "SnocVectBits8" [Show]
