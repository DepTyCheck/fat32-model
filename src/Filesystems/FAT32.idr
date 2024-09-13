module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.FinInc
import public Data.Fuel
import public Deriving.DepTyCheck.Gen
import public Derive.Show
import public Language.Reflection.Derive

%default total

public export
record NodeParams where
    constructor MkNodeParams
    clusterSize : Nat
    clusterSizeNZ : NonZero clusterSize

public export
data Node : NodeParams -> (n : Nat) -> FinInc n -> Type where
    File : forall clustSize, clustNZ, n.
           {0 k : FinInc (n * clustSize)} ->
           Node (MkNodeParams clustSize clustNZ) n (divCeilFlip clustSize @{clustNZ} k)

namespace HVectNode
    public export
    data HVectNode : NodeParams -> (k : Nat) -> (ns : VectNat k) -> HVectFinInc k ns -> Type where
        Nil : HVectNode cfg 0 [] []
        (::) : forall cfg, n, ns.
               {0 cur : FinInc n} ->
               {0 cs : HVectFinInc k ns} ->
               Node cfg n cur -> 
               HVectNode cfg k ns cs -> 
               HVectNode cfg (S k) (n :: ns) (cur :: cs)

public export
data Filesystem : NodeParams -> Nat -> Type where
    Root : {0 clustSize : Nat} ->
           {0 clustNZ : NonZero clustSize} ->
           {0 n : Nat} ->
           {0 k : Nat} ->
           {0 klte : LTE k (divNatNZ (n * clustSize) 32 SIsNonZero)} ->
           {0 ns : VectNat k} ->
           {0 cs : HVectFinInc k ns} ->
           (entries : HVectNode (MkNodeParams clustSize clustNZ) k ns cs) ->
           Filesystem (MkNodeParams clustSize clustNZ) (n + sum ns)

public export
genFilesystem : Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust)

