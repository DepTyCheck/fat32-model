module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.FinInc
import public Data.Fuel
import public Deriving.DepTyCheck.Gen

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
          (entries : HVectMaybeNode (MkNodeParams clustSize clustNZ) (finIncToNat k) ns ms cs ts) ->
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
           -- {0 k : FinInc (divNatNZ (n * clustSize) DirentSize SIsNonZero)} ->
           {0 k : Nat} ->
           (0 klte : LTE k (divNatNZ (n * clustSize) DirentSize SIsNonZero)) =>
           {0 ns : VectNat k} ->
           {0 ms : VectNat k} ->
           {0 cs : HVectFinInc k ns} ->
           {0 ts : HVectFinInc k ms} ->
           (entries : HVectMaybeNode (MkNodeParams clustSize clustNZ) k ns ms cs ts) ->
           Filesystem (MkNodeParams clustSize clustNZ) (n + sum ms)

public export
genFilesystem : Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust)
