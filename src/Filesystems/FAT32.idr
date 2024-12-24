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
    File : (0 clustNZ : IsSucc clustSize) =>
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
    Root : (0 clustNZ : IsSucc clustSize) =>
           {0 klte : LTE k (divNatNZ (n * clustSize) DirentSize %search)} ->
           (entries : HVectMaybeNode (MkNodeParams clustSize) k ns ms cs ts) ->
           Filesystem (MkNodeParams clustSize) (n + sum ms)

public export
genFilesystem : Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust)


public export
data NodeB : {0 c : FinInc n} -> {0 t : FinInc m} -> Node cfg n m c t -> Type

namespace MaybeNodeB
    public export
    data MaybeNodeB : {0 c : FinInc n} -> {0 t : FinInc m} -> MaybeNode cfg n m c t -> Type where
        Nothing : MaybeNodeB Nothing
        Just : NodeB node -> MaybeNodeB (Just node)

namespace HVectMaybeNodeB
    public export
    data HVectMaybeNodeB : (cfg : NodeParams) -> (k : Nat) -> {0 ns : VectNat k} -> {0 ms : VectNat k} -> {0 cs : HVectFinInc k ns} -> {0 ts : HVectFinInc k ms} -> HVectMaybeNode cfg k ns ms cs ts -> Type where
        Nil : HVectMaybeNodeB cfg 0 []
        (::) : {0 ns : VectNat k} ->
               {0 ms : VectNat k} ->
               {0 cs : HVectFinInc k ns} ->
               {0 ts : HVectFinInc k ms} ->
               {0 node : MaybeNode cfg n m c t} ->
               {0 nodes : HVectMaybeNode cfg k ns ms cs ts} ->
               MaybeNodeB node -> 
               HVectMaybeNodeB cfg k nodes -> 
               HVectMaybeNodeB cfg (S k) (node :: nodes)

public export
data NodeB : {0 c : FinInc n} -> {0 t : FinInc m} -> Node cfg n m c t -> Type where
    FileB : VectBits8 FilenameLength -> 
            VectBits8 (cv * clustSize) -> 
            (node : Node cfg n n (MkFinInc cv cp) (MkFinInc cv cp)) -> 
            NodeB node
    DirB : (0 clustNZ : IsSucc clustSize) =>
           {0 ents : HVectMaybeNode (MkNodeParams clustSize) kv ns ms cs ts} ->
           VectBits8 FilenameLength ->
           (nodes : HVectMaybeNodeB (MkNodeParams clustSize) kv ents) ->
           NodeB (Dir meta ents {n})

public export
data FilesystemB : Filesystem cfg sz -> Type where
    RootB : (0 clustNZ : IsSucc clustSize) =>
            {0 ents : HVectMaybeNode (MkNodeParams clustSize) k ns ms cs ts} ->
            (nodes : HVectMaybeNodeB (MkNodeParams clustSize) k ents) ->
            FilesystemB (Root ents {n})

public export
genFilesystemB : (fs : Filesystem cfg sz) -> Gen NonEmpty (FilesystemB fs)


%language ElabReflection
%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeParams" [Show]
%runElab derive "Metadata" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HVectMaybeNode"]
%runElab deriveIndexed "Filesystem" [Show]
