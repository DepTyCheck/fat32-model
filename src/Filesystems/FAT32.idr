module Filesystems.FAT32

import Data.Nat
import Data.Nat.Division
import Data.Monomorphic.Vect
import Data.FinInc
import Syntax.PreorderReasoning

%default total

numerMinusModIsDenomMultQuot : (0 a : Nat) -> (0 b : Nat) -> (0 nz : NonZero b) => minus a (modNatNZ a b nz) = b * divNatNZ a b nz
numerMinusModIsDenomMultQuot a b = Calc $
    |~ (a `minus` modNatNZ a b nz)
    ~~ (modNatNZ a b nz + divNatNZ a b nz * b `minus` modNatNZ a b nz) ...(cong (`minus` modNatNZ a b nz) $ DivisionTheorem a b nz nz)
    ~~ (divNatNZ a b nz * b) ...(minusPlus $ modNatNZ a b nz)
    ~~ (b * divNatNZ a b nz) ...(multCommutative (divNatNZ a b nz) b)

namespace Constants
    public export
    DirentSize : Nat
    DirentSize = 32

    public export
    FilenameLength : Nat
    FilenameLength = 11

record Config where
    constructor MkConfig
    clusterSize : Nat
    clusterSizeNZ : NonZero clusterSize
    maxClusters : Nat

data Metadata : Type where

data Node : Config -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type

namespace MaybeNode
    public export
    data MaybeNode : Config -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
        Nothing : MaybeNode cfg n m cur tot
        Just : Node cfg n m tot cur -> MaybeNode cfg n m tot cur

namespace HVectMaybeNode
    public export
    data HVectMaybeNode : (k : Nat) -> (ns : VectNat k) -> (ms : VectNat k) -> HVectFinInc k ns -> HVectFinInc k ms -> Type where
        Nil : HVectMaybeNode 0 [] [] [] []
        (::) : forall cfg, n, ns, m, ms.
               {0 cur : FinInc n} ->
               {0 tot : FinInc m} ->
               {0 cs : HVectFinInc k ns} ->
               {0 ts : HVectFinInc k ms} ->
               MaybeNode cfg n m cur tot -> 
               HVectMaybeNode k ns ms cs ts -> 
               HVectMaybeNode (S k) (n :: ns) (m :: ms) (cur :: cs) (tot :: ts)

data Node : Config -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
    File : forall cfg, n, m.
           {0 k : FinInc (n * cfg.clusterSize)} ->
           (meta : Metadata) ->
           (contents : VectBits8 (finIncToNat k)) ->
           let clusterNum = divCeilFlip cfg.clusterSize @{cfg.clusterSizeNZ} k in Node cfg n n clusterNum clusterNum
    Dir : {0 cfg : Config} ->
          {0 n : Nat} ->
          {0 k : FinInc (divNatNZ (n * cfg.clusterSize) DirentSize SIsNonZero)} ->
          {0 ns : VectNat (finIncToNat k)} ->
          {0 ms : VectNat (finIncToNat k)} ->
          {0 cs : HVectFinInc (finIncToNat k) ns} ->
          {0 ts : HVectFinInc (finIncToNat k) ms} ->
          (meta : Metadata) ->
          (entries : HVectMaybeNode (finIncToNat k) ns ms cs ts) ->
          let clusterNum = divCeilFlipWeak cfg.clusterSize @{cfg.clusterSizeNZ} (rewrite numerMinusModIsDenomMultQuot (n * cfg.clusterSize) DirentSize in DirentSize * k) {r = modNatNZ (n * cfg.clusterSize) DirentSize SIsNonZero} in 
          Node cfg n (n + sum ms) clusterNum (clusterNum + sum ts)
