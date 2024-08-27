module Filesystems.FAT32

import Data.Nat
import Data.Nat.Division
import Data.Monomorphic.Vect
import Data.FinInc
import Data.Fuel
import Deriving.DepTyCheck.Gen

%default total


namespace Constants
    public export
    DirentSize : Nat
    DirentSize = 32

    public export
    FilenameLength : Nat
    FilenameLength = 11

public export
record NodeParams where
    constructor MkNodeParams
    clusterSize : Nat
    clusterSizeNZ : NonZero clusterSize

-- public export
-- record FSConfig where
--     constructor MkFSConfig
--     nodeParams : NodeParams
--     maxClusters : Nat

public export
record Metadata where
    constructor MkMetadata
    -- filename : VectBits8 FilenameLength
    readOnly : Bool
    hidden : Bool
    system : Bool
    archive : Bool

public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type

namespace MaybeNode
    public export
    data MaybeNode : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
        Nothing : MaybeNode cfg n m cur tot
        Just : Node cfg n m tot cur -> MaybeNode cfg n m tot cur

namespace HVectMaybeNode
    public export
    data HVectMaybeNode : NodeParams -> (k : Nat) -> (ns : VectNat k) -> (ms : VectNat k) -> HVectFinInc k ns -> HVectFinInc k ms -> Type where
        Nil : HVectMaybeNode cfg 0 [] [] [] []
        (::) : forall cfg, n, ns, m, ms.
               {0 cur : FinInc n} ->
               {0 tot : FinInc m} ->
               {0 cs : HVectFinInc k ns} ->
               {0 ts : HVectFinInc k ms} ->
               MaybeNode cfg n m cur tot -> 
               HVectMaybeNode cfg k ns ms cs ts -> 
               HVectMaybeNode cfg (S k) (n :: ns) (m :: ms) (cur :: cs) (tot :: ts)

public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
    File : forall clustSize, clustNZ, n, m.
           {0 k : FinInc (n * clustSize)} ->
           (meta : Metadata) ->
           Node (MkNodeParams clustSize clustNZ) n n (divCeilFlip clustSize @{clustNZ} k) (divCeilFlip clustSize @{clustNZ} k)
    Dir : forall clustSize, clustNZ, n.
          {0 k : FinInc (divNatNZ (n * clustSize) DirentSize SIsNonZero)} ->
          {0 ns : VectNat (finIncToNat k)} ->
          {0 ms : VectNat (finIncToNat k)} ->
          {0 cs : HVectFinInc (finIncToNat k) ns} ->
          {0 ts : HVectFinInc (finIncToNat k) ms} ->
          (meta : Metadata) ->
          (entries : HVectMaybeNode cfg (finIncToNat k) ns ms cs ts) ->
          -- let clusterNum = divCeilFlipWeak clustSize 
          --                                   @{clustNZ} 
          --                                   (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * k) {n}
          --                                   {r = modNatNZ (n * clustSize) DirentSize SIsNonZero} 
          Node (MkNodeParams clustSize clustNZ) n (n + sum ms) (divCeilFlipWeak clustSize 
                                            @{clustNZ} 
                                            (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * k)
                                            {r = modNatNZ (n * clustSize) DirentSize SIsNonZero}) ((divCeilFlipWeak clustSize 
                                            @{clustNZ} 
                                            (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * k) {n}
                                            {r = modNatNZ (n * clustSize) DirentSize SIsNonZero}) + sum ts)

public export
data Filesystem : NodeParams -> Nat -> Type where
    Root : {0 clustSize : Nat} ->
           {0 clustNZ : NonZero clustSize} ->
           {0 n : Nat} ->
           {0 k : FinInc (divNatNZ (n * clustSize) DirentSize SIsNonZero)} ->
           {0 ns : VectNat (finIncToNat k)} ->
           {0 ms : VectNat (finIncToNat k)} ->
           {0 cs : HVectFinInc (finIncToNat k) ns} ->
           {0 ts : HVectFinInc (finIncToNat k) ms} ->
           (entries : HVectMaybeNode cfg (finIncToNat k) ns ms cs ts) ->
           Filesystem (MkNodeParams clustSize clustNZ) (n + sum ms)

public export
genFilesystem : Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust)
