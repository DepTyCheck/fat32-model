module Filesystems.FAT32

import Data.Nat
import Data.Nat.Division
import Data.Monomorphic.Vect
import Data.FinInc

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

public export
record FSConfig where
    constructor MkFSConfig
    nodeParams : NodeParams
    maxClusters : Nat

public export
record Metadata where
    constructor MkMetadata
    filename : VectBits8 FilenameLength
    readOnly : Bool
    hidden : Bool
    system : Bool
    archive : Bool

public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type

-- TODO: make the type be indexed by NodeParams
namespace MaybeNode
    public export
    data MaybeNode : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
        Nothing : MaybeNode cfg n m cur tot
        Just : Node cfg n m tot cur -> MaybeNode cfg n m tot cur

-- TODO: make the type be indexed by NodeParams
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

-- TODO: replace explicit VectBits8 blobs with their sizes
-- TODO: replace cfg.clusterSize with explicit pattern-matching
-- TODO: remove let (?)
public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
    File : forall cfg, n, m.
           {0 k : FinInc (n * cfg.clusterSize)} ->
           (meta : Metadata) ->
           (contents : VectBits8 (finIncToNat k)) ->
           let clusterNum = divCeilFlip cfg.clusterSize @{cfg.clusterSizeNZ} k in Node cfg n n clusterNum clusterNum
    Dir : {0 cfg : NodeParams} ->
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

public export
data Filesystem : FSConfig -> Type where
    Root : {0 clusterSize : Nat} ->
           {0 clusterSizeNZ : NonZero clusterSize} ->
           {0 n : Nat} ->
           {0 k : FinInc (divNatNZ (n * clusterSize) DirentSize SIsNonZero)} ->
           {0 ns : VectNat (finIncToNat k)} ->
           {0 ms : VectNat (finIncToNat k)} ->
           {0 cs : HVectFinInc (finIncToNat k) ns} ->
           {0 ts : HVectFinInc (finIncToNat k) ms} ->
           (entries : HVectMaybeNode (finIncToNat k) ns ms cs ts) ->
           -- TODO: make (n + sum ts) a generated parameter
           Filesystem (MkFSConfig (MkNodeParams clusterSize clusterSizeNZ) (n + sum ms))
    

