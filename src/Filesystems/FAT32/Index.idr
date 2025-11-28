module Filesystems.FAT32.Index

import Filesystems.FAT32
import Data.DPair
import Derive.Prelude

%default total
%prefix_record_projections off
%hide Data.Nat.divCeilNZ
%language ElabReflection


public export
data IndexDirLabel = FileI | DirI

namespace HSnocVectMaybeNode
    public export
    data IndexIn : HSnocVectMaybeNode cfg k ars wb nm -> IndexDirLabel -> Type

    public export
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb nm} -> (idx : IndexIn sx dirl) -> Node cfg ar wb nm Rootless -> Type

    public export
    Uninhabited (HSnocVectMaybeNode.AtIndex {dirl=DirI} idx (File @{clustNZ} meta blob))
    
    public export
    indexGet : (vect : HSnocVectMaybeNode cfg k ars wb nm) -> (idx : IndexIn vect dirl) -> Exists (\ar' => (nd : Node cfg ar' wb nm Rootless ** AtIndex idx nd))

    public export
    indexUpd : (cfg : NodeCfg) ->
               (ars : SnocVectNodeArgs k) ->
               (vect : HSnocVectMaybeNode cfg k ars wb nm) ->
               (idx : IndexIn vect dirl) ->
               (f : forall ar1. (curr : Node cfg ar1 wb nm Rootless) -> AtIndex idx curr -> (ar2 ** Node cfg ar2 wb nm Rootless)) ->
               (ars' ** HSnocVectMaybeNode cfg k ars' wb nm)
    
    public export
    indexUpd_ : (cfg : NodeCfg) ->
                (ars : SnocVectNodeArgs k) ->
                (vect : HSnocVectMaybeNode cfg k ars wb nm) ->
                (idx : IndexIn vect dirl) ->
                (f : forall ar1. Node cfg ar1 wb nm Rootless -> Node cfg ar1 wb nm Rootless) ->
                HSnocVectMaybeNode cfg k ars wb nm
    
    public export
    indexSet : (cfg : NodeCfg) ->
               (ars : SnocVectNodeArgs k) ->
               (vect : HSnocVectMaybeNode cfg k ars wb nm) ->
               (idx : IndexIn vect dirl) ->
               {ar2 : NodeArgs} ->
               Node cfg ar2 wb nm Rootless ->
               (ars' ** HSnocVectMaybeNode cfg k ars' wb nm)

namespace Node
    public export
    data IndexIn : Node cfg ar wb nm fs -> RootLabel -> IndexDirLabel -> Type where
        HereFile : IndexIn (File @{clustNZ} meta blob) Rootless FileI 
        HereDir : IndexIn (Dir @{clustNZ} meta names entries) Rootless DirI
        HereRoot : IndexIn (Root @{clustNZ} names entries) Rootful DirI
        ThereDir : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs dirl -> IndexIn (Dir @{clustNZ} meta names xs) Rootless dirl
        ThereRoot : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs dirl -> IndexIn (Root @{clustNZ} {k} names xs) Rootless dirl

    -- %runElab deriveIndexed "IndexIn" [Show]

    public export
    data AtIndex : {node : Node cfg ar wb nm fs} -> (idx : IndexIn node rootl dirl) -> Node cfg ar' wb nm fs' -> Type where
        [search node idx]
        HereFile' : AtIndex {node=File @{clustNZ} meta blob} HereFile $ File @{clustNZ} meta blob 
        HereDir' : AtIndex {node=Dir @{clustNZ} meta names entries} HereDir $ Dir @{clustNZ} meta names entries
        HereRoot' : AtIndex {node=Root @{clustNZ} names entries} HereRoot $ Root @{clustNZ} names entries
        ThereDir' : AtIndex {cfg = MkNodeCfg clustSize @{clustNZ}} {sx} i nd -> AtIndex {node = Dir @{clustNZ} meta names sx} (ThereDir i) nd
        ThereRoot' : AtIndex {cfg = MkNodeCfg clustSize @{clustNZ}} {sx} i nd -> AtIndex {node = Root @{clustNZ} names sx} (ThereRoot i) nd

    public export
    Uninhabited (Node.AtIndex {dirl=DirI} idx (File @{clustNZ} meta blob)) where
      uninhabited (ThereDir' x) = uninhabited x
      uninhabited (ThereRoot' x) = uninhabited x

    public export
    indexGet : (node : Node cfg ar wb nm fs) -> (idx : IndexIn node rootl dirl) -> Exists (\ar' => (nd : Node cfg ar' wb nm rootl ** AtIndex idx nd))
    indexGet f@(.(File _ _ @{_})) HereFile = Evidence _ (f ** HereFile')
    indexGet f@(.(Dir _ _ _ @{_})) HereDir = Evidence _ (f ** HereDir')
    indexGet f@(.(Root _ _ @{_})) HereRoot = Evidence _ (f ** HereRoot')
    indexGet (Dir {ars} _ _ xs @{_}) (ThereDir idx) {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexGet xs idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** ThereDir' prf)
    indexGet (Root {ars} _ xs @{_}) (ThereRoot idx) {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexGet xs idx)
      _ | (Evidence _ (nd ** prd)) = Evidence _ (nd ** ThereRoot' prd)
    indexGet .(File _ _ @{_}) (ThereDir _) impossible

    public export
    indexUpd : (cfg : NodeCfg) ->
               (node : Node cfg ar wb nm fs) ->
               (idx : IndexIn node rootl dirl) ->
               (f : forall ar1. (curr : Node cfg ar1 wb nm rootl) -> AtIndex idx curr -> (ar2 ** Node cfg ar2 wb nm rootl)) ->
               (ar' ** Node cfg ar' wb nm fs)
    indexUpd _ nd@(.(File _ _ @{_})) HereFile f = f nd HereFile'
    indexUpd _ nd@(.(Dir _ _ _ @{_})) HereDir f = f nd HereDir'
    indexUpd _ nd@(.(Root _ _ @{_})) HereRoot f = f nd HereRoot'
    indexUpd cfg@(MkNodeCfg _) (Dir {ars} meta names xs) (ThereDir idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd cfg ars xs idx (\curr', ati' => f curr' (ThereDir' ati')))
        _ | (ars' ** xs') = (_ ** Dir meta names xs')
    indexUpd cfg@(MkNodeCfg _) (Root {ars} names xs) (ThereRoot idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd cfg ars xs idx (\curr', ati' => f curr' (ThereRoot' ati')))
        _ | (ars' ** xs') = (_ ** Root names xs')
    indexUpd _ .(File _ _ @{_}) (ThereDir _) _ impossible

    public export
    indexUpd_ : (cfg : NodeCfg) ->
                (node : Node cfg ar wb nm fs) ->
                (idx : IndexIn node rootl dirl) ->
                (f : forall ar1. Node cfg ar1 wb nm rootl -> Node cfg ar1 wb nm rootl) ->
                Node cfg ar wb nm fs
    indexUpd_ _ nd@(.(File _ _ @{_})) HereFile f = f nd
    indexUpd_ _ nd@(.(Dir _ _ _ @{_})) HereDir f = f nd
    indexUpd_ _ nd@(.(Root _ _ @{_})) HereRoot f = f nd
    indexUpd_ cfg@(MkNodeCfg _) (Dir {ars} meta names xs) (ThereDir idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd_ cfg ars xs idx f)
        _ | xs' = Dir meta names xs'
    indexUpd_ cfg@(MkNodeCfg _) (Root {ars} names xs) (ThereRoot idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd_ cfg ars xs idx f)
        _ | xs' = Root names xs'
    indexUpd_ _ .(File _ _ @{_}) (ThereDir _) _ impossible

    public export
    indexSet : (cfg : NodeCfg) ->
               (node : Node cfg ar wb nm fs) ->
               (idx : IndexIn node rootl dirl) ->
               {ar2 : NodeArgs} ->
               Node cfg ar2 wb nm rootl ->
               (ar' ** Node cfg ar' wb nm fs)
    indexSet _ nd@(.(File _ _ @{_})) HereFile f = (_ ** f)
    indexSet _ nd@(.(Dir _ _ _ @{_})) HereDir f = (_ ** f)
    indexSet _ nd@(.(Root _ _ @{_})) HereRoot f = (_ ** f)
    indexSet cfg@(MkNodeCfg _) (Dir {ars} meta names xs) (ThereDir idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexSet cfg ars xs idx f)
        _ | (_ ** xs') = (_ ** Dir meta names xs')
    indexSet cfg@(MkNodeCfg _) (Root {ars} names xs) (ThereRoot idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexSet cfg ars xs idx f)
        _ | (_ ** xs') = (_ ** Root names xs')
    indexSet _ .(File _ _ @{_}) (ThereDir _) _ impossible

namespace HSnocVectMaybeNode
    data IndexIn : HSnocVectMaybeNode cfg k ars wb nm -> IndexDirLabel -> Type where
        Here : IndexIn {ar} x Rootless dirl -> IndexIn {ars = ars :< ar} ((:<) {ar} xs (Just x)) dirl
        There : IndexIn xs dirl -> IndexIn (xs :< x) dirl

    -- %runElab deriveIndexed "IndexIn" [Show]
    
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb nm} -> (idx : IndexIn sx dirl) -> Node cfg ar wb nm Rootless -> Type where
        [search sx idx]
        Here' : AtIndex {ar} {node = x} i nd -> AtIndex {ars = ars :< ar} {sx = (:<) {ar} sx (Just x)} (Here i) nd
        There' : AtIndex {sx} i nd -> AtIndex {sx = sx :< x} (There i) nd
    
    Uninhabited (HSnocVectMaybeNode.AtIndex {dirl=DirI} idx (File @{clustNZ} meta blob)) where
      uninhabited (Here' x) = uninhabited x
      uninhabited (There' x) = uninhabited x

    indexGet (_ :< Just x) (Here idx) with (indexGet x idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** Here' prf)
    indexGet (xs :< _) (There idx) with (indexGet xs idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** There' prf)

    indexUpd cfg (_ :< ar) (xs :< Just x) (Here idx) f with (indexUpd cfg x idx (\curr', ati' => f curr' (Here' ati')))
        _ | (_ ** nd) = (_ ** (xs :< Just nd))
    indexUpd cfg (ars :< _) (xs :< x) (There idx) f with (indexUpd cfg ars xs idx (\curr', ati' => f curr' (There' ati')))
        _ | (_ ** xs') = (_ ** (xs' :< x))
    
    indexUpd_ cfg (_ :< ar) (xs :< Just x) (Here idx) f with (indexUpd_ cfg x idx f)
        _ | nd = xs :< Just nd
    indexUpd_ cfg (ars :< _) (xs :< x) (There idx) f with (indexUpd_ cfg ars xs idx f)
        _ | xs' = xs' :< x
    
    indexSet cfg (_ :< ar) (xs :< Just x) (Here idx) f with (indexSet cfg x idx f)
        _ | (_ ** nd) = (_ ** (xs :< Just nd))
    indexSet cfg (ars :< _) (xs :< x) (There idx) f with (indexSet cfg ars xs idx f)
        _ | (_ ** xs') = (_ ** (xs' :< x))

