module Filesystems.FAT32.Index

import Filesystems.FAT32

%default total
%prefix_record_projections off

public export
data IndexRootLabel = MaybeRoot | NonRoot

public export
data IndexDirLabel = FileDir | OnlyDir

namespace HSnocVectMaybeNode
    public export
    data IndexIn : HSnocVectMaybeNode cfg k ars wb fs -> IndexRootLabel -> IndexDirLabel -> Type

    public export
    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb fs} -> (idx : IndexIn sx rootl dirl) -> Node cfg ar wb fs -> Type

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

    -- public export
    -- indexGet : (node : Node cfg ar wb fs) -> (idx : IndexIn node rootl dirl) -> (ar' ** fs' ** nd : Node cfg ar' wb fs' ** AtIndex idx nd)
    -- indexGet (File {k} _) (HereFile {clustNZ}) {ar=MkNodeArgs (divCeilNZ k clustSize @{clustNZ}) _} = ?indexGet_rhs_0
    -- indexGet (FileB _ _) HereFileB = ?indexGet_rhs_1
    -- indexGet (Dir _ _) HereDir = ?indexGet_rhs_2
    -- indexGet (Root _) HereRoot = ?indexGet_rhs_3
    -- indexGet (Dir meta xs) (ThereDir x) = ?indexGet_rhs_4
    -- indexGet (Root xs) (ThereRoot x) = ?indexGet_rhs_5


namespace HSnocVectMaybeNode
    data IndexIn : HSnocVectMaybeNode cfg k ars wb fs -> IndexRootLabel -> IndexDirLabel -> Type where
        Here : IndexIn {ar} x rootl dirl -> IndexIn {ars = ars :< ar} ((:<) {ar} xs (Just x)) rootl dirl
        There : IndexIn xs rootl dirl -> IndexIn (xs :< x) rootl dirl

    data AtIndex : {sx : HSnocVectMaybeNode cfg k ars wb fs} -> (idx : IndexIn sx rootl dirl) -> Node cfg ar wb fs -> Type where
        [search sx idx]
        Here' : AtIndex {ar} {node = x} i nd -> AtIndex {ars = ars :< ar} {sx = (:<) {ar} sx (Just x)} (Here i) nd
        There' : AtIndex {sx} i nd -> AtIndex {sx = sx :< x} (There i) nd
