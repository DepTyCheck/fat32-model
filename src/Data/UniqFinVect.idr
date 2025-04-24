module Data.UniqFinVect

import Filesystems.FAT32
import Deriving.DepTyCheck.Gen
import Data.Array.Core
import Data.Array.Indexed
import Derive.Prelude
import Data.Array.Core
import Data.Array.Mutable
import Control.Monad.Pure
import Data.SnocVect
import Data.Linear.Traverse1

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

%language ElabReflection
%runElab deriveIndexed "UniqFinVect" [Show]

public export
genFin : (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin n = do
    (c ** cp) <- elements' $ the (List _) $ boundedRangeDLT 0 n
    pure $ natToFinLT c @{cp}

-- boundedVect' : (b : Nat) -> SnocVect b $ Subset Nat (`LT` b)
-- boundedVect' 0 = [<]
-- boundedVect' 1 = [< (Element 0 (LTESucc LTEZero))]
-- boundedVect' (S $ S k) with (boundedVect' $ S k)
--   boundedVect' (S $ S k) | (sx :< x@(Element _ prf)) = sx :< x :< (Element (S $ S k) $ LTESucc {right=S k} prf) 
-- -- boundedVect' b 0 = [<]
-- -- boundedVect' b (S k) with (decomposeLte 0 b LTEZero)
-- --   boundedVect' b (S k) | (Right peq) = []
-- --   boundedVect' b (S k) | (Left plt) with (boundedRange' b k)
-- --     boundedVect' b (S k) | (Left plt) | ps = (Element a plt) :: ps
--
-- public export
-- boundedVectLT : (b : Nat) -> Vect b $ Subset Nat (`LT` b)
-- boundedVectLT b = asVect $ boundedVect' b


allFins'' : (k : Nat) -> SnocVect k (Fin k)
allFins'' 0 = [<]
allFins'' 1 = [< FZ]
allFins'' (S $ S k) = let sx := allFins'' (S k) in believe_me sx :< FS (deah sx)

allFins' : (n : Nat) -> Vect n (Fin n)
allFins' n = asVect $ allFins'' n

ontoVect : (sx : SnocList a) -> Vect n a -> Vect (length sx + n) a
ontoVect [<]       xs = xs
ontoVect (sx :< x) xs =
  rewrite plusSuccRightSucc (length sx) n in ontoVect sx (x::xs)

traverse1Vect' :
     (sx : SnocList b)
  -> (forall n'. a -> Vect n' a -> F1 s b)
  -> Vect n a
  -> F1 s (Vect (length sx + n) b)
traverse1Vect'           sx f []        t = ontoVect sx [] # t
traverse1Vect' {n = S k} sx f xxs@(x :: xs) t =
  let Token.(#) v t1 := f x xxs t
   in rewrite sym (plusSuccRightSucc (length sx) k)
      in traverse1Vect' (sx :< v) f xs t1

traverse1' :
  (forall n'. a -> Vect n' a -> F1 s b)
  -> Vect n a
  -> F1 s (Vect n b)
traverse1' = traverse1Vect' [<]

forSuf : Applicative f => Vect n a -> (forall m. Vect m a -> f b) -> f (Vect n b)
forSuf [] g = pure []
forSuf xxs@(x :: xs) g = [| g xxs :: forSuf xs g |]

for1 : Vect n a -> (1 t : T1 s) -> (forall n'. a -> Vect n' a -> F1 s b) -> R1 s (Vect n b)
for1 x t g = traverse1' g x t

-- public export
-- genMap : (k : Nat) -> (n : Nat) -> Gen MaybeEmpty $ Vect k (Fin n)
-- genMap k n = run1 $ \t => do
--     let ar # t = unsafeMArray1 n t
--         () # t = writeVect ar (allFins' n) t
--         xs # t = for1 (allFins' k) t $ \i, is, t => do
--             j <- elements' is
--             let vi # t = get ar i t
--                 vj # t = get ar j t
--                 () # t = set ar j vi t
--             (pure vj) # t
--     ?amogus

public export
genMap : (k : Nat) -> (n : Nat) -> (0 _ : IsSucc k) => Gen MaybeEmpty $ Vect k (Fin $ k + n)
genMap k@(S k') n = do
    let xs = allFins' $ k + n
    let ys = weakenN n <$> allFins' k
    rands <- for ys $ \x => choose (x, last)
    let zs = runPure $ do
        ar <- unsafeMArray $ k + n
        lift1 $ writeVect ar xs
        for (zip rands ys) $ \(j, i) => do
            vi <- lift1 $ get ar i
            vj <- lift1 $ get ar j
            lift1 $ set ar j vi
            pure vj
    pure zs
