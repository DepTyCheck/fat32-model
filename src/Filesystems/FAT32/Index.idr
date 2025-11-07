module Filesystems.FAT32.Index

import Filesystems.FAT32
import Data.DPair

%default total
%prefix_record_projections off
%hide Data.Nat.divCeilNZ

-- TODO:Consider changing labels to something like "Root | NonRoot" in order to reduce ambiguity in types (like the fs parameter) 
public export
data IndexRootLabel = RootI | NonRootI

Eq IndexRootLabel where
  RootI == RootI = True
  NonRootI == NonRootI = True
  _ == _ = False

public export
data IndexDirLabel = FileI | DirI

namespace HSnocVectMaybeNode
    public export
    data IndexIn : HSnocVectMaybeNode cfg k ars wb -> IndexDirLabel -> Type

    public export
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb} -> (idx : IndexIn sx dirl) -> Node cfg ar wb False -> Type
    
    public export
    indexGet : (vect : HSnocVectMaybeNode cfg k ars wb) -> (idx : IndexIn vect dirl) -> Exists (\ar' => (nd : Node cfg ar' wb False ** AtIndex idx nd))

namespace Node
    
    public export
    data IndexIn : Node cfg ar wb fs -> IndexRootLabel -> IndexDirLabel -> Type where
        HereFile : IndexIn (File @{clustNZ} meta) NonRootI FileI 
        HereFileB : IndexIn (FileB @{clustNZ} meta blob) NonRootI FileI
        HereDir : IndexIn (Dir @{clustNZ} meta entries) NonRootI DirI
        HereRoot : IndexIn (Root @{clustNZ} entries) RootI DirI
        ThereDir : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs dirl -> IndexIn (Dir @{clustNZ} meta xs) NonRootI dirl
        ThereRoot : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs dirl -> IndexIn (Root @{clustNZ} xs) NonRootI dirl

    public export
    data AtIndex : {node : Node cfg ar wb fs} -> (idx : IndexIn node rootl dirl) -> Node cfg ar' wb fs' -> Type where
        [search node idx]
        HereFile' : AtIndex HereFile node
        HereFileB' : AtIndex HereFileB node
        HereDir' : AtIndex HereDir node
        HereRoot' : AtIndex HereRoot node
        ThereDir' : AtIndex {cfg = MkNodeCfg clustSize @{clustNZ}} {sx} i nd -> AtIndex {node = Dir @{clustNZ} meta sx} (ThereDir i) nd
        ThereRoot' : AtIndex {cfg = MkNodeCfg clustSize @{clustNZ}} {sx} i nd -> AtIndex {node = Root @{clustNZ} sx} (ThereRoot i) nd

    public export
    indexGet : (node : Node cfg ar wb fs) -> (idx : IndexIn node rootl dirl) -> Exists (\ar' => (nd : Node cfg ar' wb (rootl == RootI) ** AtIndex idx nd))
    indexGet f@(.(File _ @{_})) HereFile = Evidence _ (f ** HereFile')
    indexGet f@(.(FileB _ _ @{_})) HereFileB = Evidence _ (f ** HereFileB')
    indexGet f@(.(Dir _ _ @{_})) HereDir = Evidence _ (f ** HereDir')
    indexGet f@(.(Root _ @{_})) HereRoot = Evidence _ (f ** HereRoot')
-- FIXME: This probably only works because of a compiler bug (xs changes quantity from 0 to ω when matching a bogus as-pattern), may break in the future
-- TODO: Fill holes
    indexGet .(Dir _ xs @{_}) (ThereDir idx) {ar=ar@(MkNodeArgs {})} with (indexGet xs idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** ThereDir' prf)
    indexGet .(Root xs @{_}) (ThereRoot idx) {ar=ar@(MkNodeArgs {})} with (indexGet xs idx)
      _ | (Evidence _ (nd ** prd)) = Evidence _ (nd ** ThereRoot' prd)
    -- indexGet .(File _) (ThereDir _) impossible


namespace HSnocVectMaybeNode
    data IndexIn : HSnocVectMaybeNode cfg k ars wb -> IndexDirLabel -> Type where
        Here : IndexIn {ar} x NonRootI dirl -> IndexIn {ars = ars :< ar} ((:<) {ar} xs (Just x)) dirl
        There : IndexIn xs dirl -> IndexIn (xs :< x) dirl

    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb} -> (idx : IndexIn sx dirl) -> Node cfg ar wb False -> Type where
        [search sx idx]
        Here' : AtIndex {ar} {node = x} i nd -> AtIndex {ars = ars :< ar} {sx = (:<) {ar} sx (Just x)} (Here i) nd
        There' : AtIndex {sx} i nd -> AtIndex {sx = sx :< x} (There i) nd

    indexGet (_ :< Just x) (Here idx) with (indexGet x idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** Here' prf)
    indexGet (xs :< _) (There idx) with (indexGet xs idx)
      _ | (Evidence _ (nd ** prf)) = Evidence _ (nd ** There' prf)

