module Filesystems.FAT32

import Data.Nat
import Data.Fin
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

record Config where
    constructor MkConfig
    clusterSize : Nat
    maxClusters : Nat

data Metadata : Type where

data Node : Config -> (n : Nat) -> (m : Nat) -> Fin n -> Fin m -> Type

namespace MaybeNode
    public export
    data MaybeNode : Config -> (n : Nat) -> (m : Nat) -> Fin n -> Fin m -> Type where
        Nothing : MaybeNode cfg n m cur tot
        Just : Node cfg n m tot cur -> MaybeNode cfg n m tot cur

namespace HVectMaybeNode
    public export
    data HVectMaybeNode : (k : Nat) -> (n : Nat) -> (m : Nat) -> VectFin k n -> VectFin k m -> Type where
        Nil : HVectMaybeNode 0 n m [] []
        (::) : forall cfg, n, m.
               {0 cur : Fin n} ->
               {0 tot : Fin m} ->
               {0 cs : VectFin k n} ->
               {0 ts : VectFin k m} ->
               MaybeNode cfg n m cur tot -> 
               HVectMaybeNode k n m cs ts -> 
               HVectMaybeNode (S k) n m (cur :: cs) (tot :: ts)

-- TODO: Fix type by properly transitioning to `Fin`s
data Node : Config -> (n : Nat) -> (m : Nat) -> Fin n -> Fin m -> Type where
    File : forall cfg, n, m.
           {0 k : Fin ((clusterSize cfg) * n)} ->
           (meta : Metadata) ->
           (contents : VectBits8 (finToNat k)) ->
           let clusterNum = divCeil k (clusterSize cfg) in Node cfg n m clusterNum clusterNum
    Dir : forall k, cs, ts .
          (meta : Metadata) ->
          (entries : HVectMaybeNode k cs ts) ->
          let clusterNum = divCeil (DirentSize * k) (clusterSize cfg) in Node clusterNum (clusterNum + sum ts)
