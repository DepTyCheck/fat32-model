module Filesystems.FAT32.Index

import Filesystems.FAT32
import Data.DPair

%default total
%prefix_record_projections off
%hide Data.Nat.divCeilNZ

-- TODO:Consider changing labels to something like "Root | NonRoot" in order to reduce ambiguity in types (like the fs parameter) 
public export
data IndexRootLabel = MaybeRoot | NonRoot

public export
data IndexDirLabel = FileDir | OnlyDir

namespace HSnocVectMaybeNode
    public export
    data IndexIn : HSnocVectMaybeNode cfg k ars wb -> IndexRootLabel -> IndexDirLabel -> Type

    public export
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb} -> (idx : IndexIn sx rootl dirl) -> Node cfg ar wb fs -> Type

namespace Node
    
    public export
    data IndexIn : Node cfg ar wb fs -> IndexRootLabel -> IndexDirLabel -> Type where
        HereFile : IndexIn (File @{clustNZ} meta) rootl FileDir 
        HereFileB : IndexIn (FileB @{clustNZ} meta blob) rootl FileDir
        HereDir : IndexIn (Dir @{clustNZ} meta entries) rootl dirl
        HereRoot : IndexIn (Root @{clustNZ} entries) MaybeRoot dirl
        ThereDir : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs rootl dirl -> IndexIn (Dir @{clustNZ} meta xs) rootl dirl
        ThereRoot : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs rootl dirl -> IndexIn (Root @{clustNZ} xs) rootl dirl

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
    indexGet : (node : Node cfg ar wb fs) -> (idx : IndexIn node rootl dirl) -> Exists (\fs' => Exists (\ar' => (nd : Node cfg ar' wb fs' ** AtIndex idx nd)))
    indexGet f@(.(File _ @{_})) HereFile = Evidence _ $ Evidence _ (f ** HereFile')
    indexGet f@(.(FileB _ _ @{_})) HereFileB = Evidence _ $ Evidence _ (f ** HereFileB')
    indexGet f@(.(Dir _ _ @{_})) HereDir = Evidence _ $ Evidence _ (f ** HereDir')
    indexGet f@(.(Root _ @{_})) HereRoot = Evidence _ $ Evidence _ (f ** HereRoot')
-- FIXME: This probably only works because of a compiler bug (xs changes quantity from 0 to ω when matching a bogus as-pattern), may break in the future
-- TODO: Fill holes
    indexGet .(Dir _ xs @{_}) (ThereDir idx) {ar=ar@(MkNodeArgs {})} = ?indexGet_rhs_4 xs idx
    indexGet .(Root xs @{_}) (ThereRoot idx) {ar=ar@(MkNodeArgs {})} = ?indexGet_rhs_5 xs idx
    -- indexGet .(File _) (ThereDir _) impossible


namespace HSnocVectMaybeNode
    data IndexIn : HSnocVectMaybeNode cfg k ars wb -> IndexRootLabel -> IndexDirLabel -> Type where
        Here : IndexIn {ar} x rootl dirl -> IndexIn {ars = ars :< ar} ((:<) {ar} xs (Just x)) rootl dirl
        There : IndexIn xs rootl dirl -> IndexIn (xs :< x) rootl dirl

    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb} -> (idx : IndexIn sx rootl dirl) -> Node cfg ar wb fs -> Type where
        [search sx idx]
        Here' : AtIndex {ar} {node = x} i nd -> AtIndex {ars = ars :< ar} {sx = (:<) {ar} sx (Just x)} (Here i) nd
        There' : AtIndex {sx} i nd -> AtIndex {sx = sx :< x} (There i) nd

    public export
    indexGet : (vect : HSnocVectMaybeNode cfg k ars wb) -> (idx : IndexIn vect rootl dirl) -> Exists (\fs' => Exists (\ar' => (nd : Node cfg ar' wb fs' ** AtIndex idx nd)))
    indexGet (_ :< Just x) (Here idx) with (indexGet x idx)
      indexGet (_ :< Just x) (Here idx) | (Evidence _ (Evidence _ (nd ** prf))) = Evidence _ $ Evidence _ (nd ** Here' prf)
    indexGet (xs :< _) (There idx) with (indexGet xs idx)
      indexGet (xs :< _) (There idx) | (Evidence _ (Evidence _ (nd ** prf))) = Evidence _ $ Evidence _ (nd ** There' prf)

