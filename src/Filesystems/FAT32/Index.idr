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
    data IndexIn : HSnocVectMaybeNode cfg k ars prs -> IndexDirLabel -> Type

    public export
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars prs} -> (idx : IndexIn sx dirl) -> Node cfg ar Rootless -> Type

    public export
    Uninhabited (HSnocVectMaybeNode.AtIndex {dirl=DirI} idx (File @{clustNZ} meta blob))
    
    public export
    indexGet : (vect : HSnocVectMaybeNode cfg k ars prs) -> (idx : IndexIn vect dirl) -> Exists (\ar' => (nd : Node cfg ar' Rootless ** AtIndex idx nd))

    -- public export
    -- indexUpd : (cfg : NodeCfg) ->
    --            (ars : SnocVectNodeArgs k) ->
    --            (vect : HSnocVectMaybeNode cfg k ars) ->
    --            (idx : IndexIn vect dirl) ->
    --            (f : forall ar1. (curr : Node cfg ar1 Rootless) -> AtIndex idx curr -> (ar2 ** Node cfg ar2 Rootless)) ->
    --            (ars' ** HSnocVectMaybeNode cfg k ars')
    
    public export
    indexUpd_ : (cfg : NodeCfg) ->
                (ars : SnocVectNodeArgs k) ->
                (vect : HSnocVectMaybeNode cfg k ars prs) ->
                (idx : IndexIn vect dirl) ->
                (f : forall ar1. Node cfg ar1 Rootless -> Node cfg ar1 Rootless) ->
                HSnocVectMaybeNode cfg k ars prs
    
    public export
    indexSet : (cfg : NodeCfg) ->
               (ars : SnocVectNodeArgs k) ->
               (vect : HSnocVectMaybeNode cfg k ars prs) ->
               (idx : IndexIn vect dirl) ->
               {ar2 : NodeArgs} ->
               Node cfg ar2 Rootless ->
               (ars' ** HSnocVectMaybeNode cfg k ars' prs)

    public export
    data NamesWeakened : (ff : UniqNames prs) -> (ff' : UniqNames prs') -> Type where
      WEmpty : NamesWeakened Empty Empty
      WErased : NamesWeakened ff ff' ->
                NamesWeakened (NewName ff f @{nprf}) (NewName ff' Nothing @{nprf'})
      WEqual : NamesWeakened ff ff' ->
               NamesWeakened (NewName ff f @{nprf}) (NewName ff' f @{nprf'})

    public export
    trivialNameWeaken : (ff : UniqNames prs) -> NamesWeakened ff ff
    trivialNameWeaken Empty = WEmpty
    trivialNameWeaken (NewName ff f) = WEqual (trivialNameWeaken ff)

    public export
    0 newNameInWeakenedPrf : (ff : UniqNames prs) ->
                             (ff' : UniqNames prs') ->
                             (f : MaybeFilename pr) ->
                             (0 w : NamesWeakened ff ff') ->
                             (0 nprf : NameIsNew ff f) ->
                             NameIsNew ff' f
    newNameInWeakenedPrf ff ff' Nothing w nprf = NewNothing
    newNameInWeakenedPrf Empty Empty (Just x) WEmpty nprf = EmptyList
    newNameInWeakenedPrf (NewName ff Nothing) (NewName ff' Nothing) (Just x) (WErased y) (OldNothing z) = OldNothing $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (NewName ff (Just f)) (NewName ff' Nothing) (Just x) (WErased y) (OldJust _ z) = OldNothing $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (NewName ff Nothing) (NewName ff' Nothing) (Just x) (WEqual y) (OldNothing z) = OldNothing $ newNameInWeakenedPrf ff ff' (Just x) y z
    newNameInWeakenedPrf (NewName ff (Just f)) (NewName ff' (Just f)) (Just x) (WEqual y) (OldJust so z) = OldJust so $ newNameInWeakenedPrf ff ff' (Just x) y z

    public export
    data ShallowIndexIn : HSnocVectMaybeNode cfg k ars prs -> Type where
        SHere : ShallowIndexIn $ xs :< Just x
        SThere : ShallowIndexIn xs -> ShallowIndexIn $ xs :< x

    public export
    shallowIndexSet : (cfg : NodeCfg) ->
                      (ars : SnocVectNodeArgs k) ->
                      (prs : SnocVectPresence k) ->
                      (vect : HSnocVectMaybeNode cfg k ars prs) ->
                      (names : UniqNames prs) ->
                      (sidx : ShallowIndexIn vect) ->
                      {ar2 : NodeArgs} ->
                      {pr2 : Presence} ->
                      (mnode : MaybeNode cfg ar2 pr2) ->
                      (ars' ** prs' ** (HSnocVectMaybeNode cfg k ars' prs', Subset (UniqNames prs') $ \ff' => NamesWeakened names ff'))
    shallowIndexSet cfg (ars :< ar) (prs :< Present) (sp :< Just p) (NewName ff f) SHere Nothing = (_ ** _ ** (sp :< Nothing, Element (NewName ff Nothing) $ WErased $ trivialNameWeaken ff))
    shallowIndexSet cfg (ars :< ar) (prs :< Present) (sp :< Just p) (NewName ff f) SHere (Just x) = (_ ** _ ** (sp :< Just x, Element (NewName ff f) $ WEqual $ trivialNameWeaken ff))
    shallowIndexSet cfg (ars :< ar) (prs :< pr) (sp :< p) (NewName ff f @{nprf}) (SThere sidx) mnode with (shallowIndexSet cfg ars prs sp ff sidx mnode)
      _ | (ars' ** prs' ** (sp', Element ff' wprf')) = (_ ** _ ** (sp' :< p, Element (NewName ff' f @{newNameInWeakenedPrf ff ff' f wprf' nprf}) $ WEqual wprf'))
    

namespace Node
    public export
    data IndexIn : Node cfg ar fs -> RootLabel -> IndexDirLabel -> Type where
        HereFile : IndexIn (File @{clustNZ} meta blob) Rootless FileI 
        HereDir : IndexIn (Dir @{clustNZ} meta entries names) Rootless DirI
        HereRoot : IndexIn (Root @{clustNZ} entries names) Rootful DirI
        ThereDir : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs dirl -> IndexIn (Dir @{clustNZ} meta xs names) Rootless dirl
        ThereRoot : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs dirl -> IndexIn (Root @{clustNZ} {k} xs names) Rootless dirl

    -- %runElab deriveIndexed "IndexIn" [Show]

    public export
    data AtIndex : {node : Node cfg ar fs} -> (idx : IndexIn node rootl dirl) -> Node cfg ar' fs' -> Type where
        [search node idx]
        HereFile' : AtIndex {node=File @{clustNZ} meta blob} HereFile $ File @{clustNZ} meta blob 
        HereDir' : AtIndex {node=Dir @{clustNZ} meta entries names} HereDir $ Dir @{clustNZ} meta entries names
        HereRoot' : AtIndex {node=Root @{clustNZ} entries names} HereRoot $ Root @{clustNZ} entries names
        ThereDir' : AtIndex {cfg = MkNodeCfg clustSize @{clustNZ}} {sx} i nd -> AtIndex {node = Dir @{clustNZ} meta sx names} (ThereDir i) nd
        ThereRoot' : AtIndex {cfg = MkNodeCfg clustSize @{clustNZ}} {sx} i nd -> AtIndex {node = Root @{clustNZ} sx names} (ThereRoot i) nd

    public export
    Uninhabited (Node.AtIndex {dirl=DirI} idx (File @{clustNZ} meta blob)) where
      uninhabited (ThereDir' x) = uninhabited x
      uninhabited (ThereRoot' x) = uninhabited x

    public export
    indexGet : (node : Node cfg ar fs) -> (idx : IndexIn node rootl dirl) -> Exists (\ar' => (nd : Node cfg ar' rootl ** AtIndex idx nd))
    indexGet f@(.(File _ _ @{_})) HereFile = Evidence _ (f ** HereFile')
    indexGet f@(.(Dir _ _ _ @{_})) HereDir = Evidence _ (f ** HereDir')
    indexGet f@(.(Root _ _ @{_})) HereRoot = Evidence _ (f ** HereRoot')
    indexGet (Dir {ars} _ xs _ @{_}) (ThereDir idx) {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexGet xs idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** ThereDir' prf)
    indexGet (Root {ars} xs _ @{_}) (ThereRoot idx) {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexGet xs idx)
      _ | (Evidence _ (nd ** prd)) = Evidence _ (nd ** ThereRoot' prd)
    indexGet .(File _ _ @{_}) (ThereDir _) impossible

    -- public export
    -- indexUpd : (cfg : NodeCfg) ->
    --            (node : Node cfg ar fs) ->
    --            (idx : IndexIn node rootl dirl) ->
    --            (f : forall ar1. (curr : Node cfg ar1 rootl) -> AtIndex idx curr -> (ar2 ** Node cfg ar2 rootl)) ->
    --            (ar' ** Node cfg ar' fs)
    -- indexUpd _ nd@(.(File _ _ @{_})) HereFile f = f nd HereFile'
    -- indexUpd _ nd@(.(Dir _ _ _ @{_})) HereDir f = f nd HereDir'
    -- indexUpd _ nd@(.(Root _ _ @{_})) HereRoot f = f nd HereRoot'
    -- indexUpd cfg@(MkNodeCfg _) (Dir {ars} meta xs names) (ThereDir idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd cfg ars xs idx (\curr', ati' => f curr' (ThereDir' ati')))
    --     _ | (ars' ** xs') = (_ ** Dir meta xs' names)
    -- indexUpd cfg@(MkNodeCfg _) (Root {ars} names xs) (ThereRoot idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd cfg ars xs idx (\curr', ati' => f curr' (ThereRoot' ati')))
    --     _ | (ars' ** xs') = (_ ** Root names xs')
    -- indexUpd _ .(File _ _ @{_}) (ThereDir _) _ impossible

    public export
    indexUpd_ : (cfg : NodeCfg) ->
                (node : Node cfg ar fs) ->
                (idx : IndexIn node rootl dirl) ->
                (f : forall ar1. Node cfg ar1 rootl -> Node cfg ar1 rootl) ->
                Node cfg ar fs
    indexUpd_ _ nd@(.(File _ _ @{_})) HereFile f = f nd
    indexUpd_ _ nd@(.(Dir _ _ _ @{_})) HereDir f = f nd
    indexUpd_ _ nd@(.(Root _ _ @{_})) HereRoot f = f nd
    indexUpd_ cfg@(MkNodeCfg _) (Dir {ars} meta xs names) (ThereDir idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd_ cfg ars xs idx f)
        _ | xs' = Dir meta xs' names
    indexUpd_ cfg@(MkNodeCfg _) (Root {ars} xs names) (ThereRoot idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexUpd_ cfg ars xs idx f)
        _ | xs' = Root xs' names
    indexUpd_ _ .(File _ _ @{_}) (ThereDir _) _ impossible

    public export
    indexSet : (cfg : NodeCfg) ->
               (node : Node cfg ar fs) ->
               (idx : IndexIn node rootl dirl) ->
               {ar2 : NodeArgs} ->
               Node cfg ar2 rootl ->
               (ar' ** Node cfg ar' fs)
    indexSet _ nd@(.(File _ _ @{_})) HereFile f = (_ ** f)
    indexSet _ nd@(.(Dir _ _ _ @{_})) HereDir f = (_ ** f)
    indexSet _ nd@(.(Root _ _ @{_})) HereRoot f = (_ ** f)
    indexSet cfg@(MkNodeCfg _) (Dir {ars} meta xs names) (ThereDir idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexSet cfg ars xs idx f)
        _ | (_ ** xs') = (_ ** Dir meta xs' names)
    indexSet cfg@(MkNodeCfg _) (Root {ars} xs names) (ThereRoot idx) f {ar=ar@(MkNodeArgs _ (_ + totsum ars))} with (indexSet cfg ars xs idx f)
        _ | (_ ** xs') = (_ ** Root xs' names)
    indexSet _ .(File _ _ @{_}) (ThereDir _) _ impossible

namespace HSnocVectMaybeNode
    data IndexIn : HSnocVectMaybeNode cfg k ars prs -> IndexDirLabel -> Type where
        Here : IndexIn {ar} x Rootless dirl -> IndexIn {ars = ars :< ar} {prs = prs :< Present} ((:<) {ar} xs (Just x)) dirl
        There : IndexIn xs dirl -> IndexIn (xs :< x) dirl

    -- %runElab deriveIndexed "IndexIn" [Show]
    
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars prs} -> (idx : IndexIn sx dirl) -> Node cfg ar Rootless -> Type where
        [search sx idx]
        Here' : AtIndex {ar} {node = x} i nd -> AtIndex {ars = ars :< ar} {prs = prs :< Present} {sx = (:<) {ar} sx (Just x)} (Here i) nd
        There' : AtIndex {sx} i nd -> AtIndex {sx = sx :< x} (There i) nd
    
    Uninhabited (HSnocVectMaybeNode.AtIndex {dirl=DirI} idx (File @{clustNZ} meta blob)) where
      uninhabited (Here' x) = uninhabited x
      uninhabited (There' x) = uninhabited x

    indexGet (_ :< Just x) (Here idx) with (indexGet x idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** Here' prf)
    indexGet (xs :< _) (There idx) with (indexGet xs idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** There' prf)

    -- indexUpd cfg (_ :< ar) (xs :< Just x) (Here idx) f with (indexUpd cfg x idx (\curr', ati' => f curr' (Here' ati')))
    --     _ | (_ ** nd) = (_ ** (xs :< Just nd))
    -- indexUpd cfg (ars :< _) (xs :< x) (There idx) f with (indexUpd cfg ars xs idx (\curr', ati' => f curr' (There' ati')))
    --     _ | (_ ** xs') = (_ ** (xs' :< x))
    
    indexUpd_ cfg (_ :< ar) (xs :< Just x) (Here idx) f with (indexUpd_ cfg x idx f)
        _ | nd = xs :< Just nd
    indexUpd_ cfg (ars :< _) (xs :< x) (There idx) f with (indexUpd_ cfg ars xs idx f)
        _ | xs' = xs' :< x
    
    indexSet cfg (_ :< ar) (xs :< Just x) (Here idx) f with (indexSet cfg x idx f)
        _ | (_ ** nd) = (_ ** (xs :< Just nd))
    indexSet cfg (ars :< _) (xs :< x) (There idx) f with (indexSet cfg ars xs idx f)
        _ | (_ ** xs') = (_ ** (xs' :< x))

