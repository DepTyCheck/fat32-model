module Filesystems.FAT32.NameTree

import Filesystems.FAT32

%default total
%prefix_record_projections off
%language ElabReflection

namespace NameTree
    public export
    data NameTree : Node cfg ar wb fs -> Type
    
    public export
    data MaybeNameTree : MaybeNode cfg ar wb fs -> Type

    public export
    data UniqNames : Nat -> Type

    public export
    data HSnocVectNameTree : HSnocVectMaybeNode cfg k ars True False -> Type where
        Lin : HSnocVectNameTree [<]
        (:<) : HSnocVectNameTree nodes -> MaybeNameTree node -> HSnocVectNameTree (nodes :< node)

    public export
    data NameIsNew : (k : Nat) -> UniqNames k -> Filename -> Type

    data NameTree : Node cfg ar wb fs -> Type where
        File : {0 clustSize : Nat} ->
               {0 clustNZ : IsSucc clustSize} ->
               {0 k : Nat} ->
               NameTree $ File @{clustNZ} meta {k}
        FileB : {0 clustSize : Nat} ->
                {0 clustNZ : IsSucc clustSize} ->
                {0 k : Nat} ->
                {0 blob : SnocVectBits8 k} ->
                NameTree $ FileB @{clustNZ} meta blob {k}
        Dir : {0 clustSize : Nat} ->
              {0 clustNZ : IsSucc clustSize} ->
              {0 k : Nat} ->
              {0 ars : SnocVectNodeArgs k} ->
              {0 nodes : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars True False} ->
              UniqNames k -> HSnocVectNameTree nodes -> NameTree $ Dir @{clustNZ} meta nodes
        Root : {0 clustSize : Nat} ->
               {0 clustNZ : IsSucc clustSize} ->
               {0 k : Nat} ->
               {0 ars : SnocVectNodeArgs k} ->
               {0 nodes : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars True False} ->
               UniqNames k -> HSnocVectNameTree nodes -> NameTree $ Root @{clustNZ} nodes

    data MaybeNameTree : MaybeNode cfg ar wb fs -> Type where
        Nothing : MaybeNameTree Nothing
        Just : NameTree node -> MaybeNameTree $ Just node

    data UniqNames : Nat -> Type where
        Empty : UniqNames Z
        NewName : (ff : UniqNames k) => (f : Filename) -> (0 _ : NameIsNew k ff f) => UniqNames (S k)

    data NameIsNew : (k : Nat) -> UniqNames k -> Filename -> Type where
        E : NameIsNew Z Empty f
        N : (0 _ : So $ x /= f) ->
            {0 ff : UniqNames k} ->
            NameIsNew k ff x ->
            {0 sub : NameIsNew k ff f} ->
            NameIsNew (S k) (NewName @{ff} f @{sub}) x

public export
genNameTree : Fuel ->
              (Fuel -> Gen MaybeEmpty Bits8) =>
              (Fuel -> Gen MaybeEmpty Filename) =>
              (cfg : NodeCfg) ->
              (ar : NodeArgs) ->
              (wb : Bool) ->
              (fs : Bool) ->
              (node : Node cfg ar wb fs) ->
              Gen MaybeEmpty $ NameTree node

%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["UniqNames", "NameTree", "MaybeNameTree", "HSnocVectNameTree"]
