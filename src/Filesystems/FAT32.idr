module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.FinInc
import public Data.Fuel
import public Deriving.DepTyCheck.Gen
import public Derive.Prelude

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
    {auto 0 clusterSizeNZ : IsSucc clusterSize}

public export
record Metadata where
    constructor MkMetadata
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
        (::) : forall cfg, n, ns, m, ms, cs, ts, cur, tot.
               MaybeNode cfg n m cur tot -> 
               HVectMaybeNode cfg k ns ms cs ts -> 
               HVectMaybeNode cfg (S k) (n :: ns) (m :: ms) (cur :: cs) (tot :: ts)

public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
    File : forall clustSize, n.
           (0 clustNZ : IsSucc clustSize) =>
           {0 k : FinInc (n * clustSize)} ->
           (meta : Metadata) ->
           Node (MkNodeParams clustSize) n n (divCeilFlip clustSize k) (divCeilFlip clustSize k)
    Dir : forall clustSize, n, kv, ns, ms, cs, ts.
          (0 clustNZ : IsSucc clustSize) =>
          {0 kp : LTE kv (divNatNZ (n * clustSize) DirentSize %search)} ->
          (meta : Metadata) ->
          (entries : HVectMaybeNode (MkNodeParams clustSize) kv ns ms cs ts) ->
          Node (MkNodeParams clustSize) n (n + sum ms) (divCeilFlipWeak clustSize 
                                            @{clustNZ} 
                                            (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * (MkFinInc kv kp))
                                            {r = modNatNZ (n * clustSize) DirentSize %search}) ((divCeilFlipWeak clustSize 
                                            @{clustNZ} 
                                            (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * (MkFinInc kv kp)) {n}
                                            {r = modNatNZ (n * clustSize) DirentSize %search}) + sum ts)

public export
data Filesystem : NodeParams -> Nat -> Type where
    Root : forall clustSize, n, k, ns, ms, cs, ts.
           (0 clustNZ : IsSucc clustSize) =>
           {0 klte : LTE k (divNatNZ (n * clustSize) DirentSize %search)} ->
           (entries : HVectMaybeNode (MkNodeParams clustSize) k ns ms cs ts) ->
           Filesystem (MkNodeParams clustSize) (n + sum ms)

public export
genFilesystem : Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust)

%language ElabReflection
%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeParams" [Show]
%runElab derive "Metadata" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HVectMaybeNode"]
%runElab deriveIndexed "Filesystem" [Show]
