module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Order
import public Data.Nat.Order.Properties
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.Fuel
import public Deriving.DepTyCheck.Gen
import public Derive.Prelude
import public Data.DPair
import Data.Bits
import public Filesystems.FAT32.Utils

%default total
%hide Data.Nat.divCeilNZ
%language ElabReflection
%prefix_record_projections off

namespace Constants
    public export
    DirentSize : Nat
    DirentSize = 32

    public export
    FilenameLengthName : Nat
    FilenameLengthName = 8

    public export
    FilenameLengthExt : Nat
    FilenameLengthExt = 3

    public export
    FilenameLength : Nat
    FilenameLength = FilenameLengthName + FilenameLengthExt

public export
data RootLabel = Rootful | Rootless

public export
data NodeCfg : Type where
    MkNodeCfg : (clustSize : Nat) ->               -- bytes per cluster
-- NOTE: clustSize must not be greater than 32K
                (0 clustNZ : IsSucc clustSize) =>
                NodeCfg

public export
record Metadata where
    constructor MkMetadata
    readOnly : Bool
    hidden : Bool
    system : Bool
    archive : Bool

public export
record NodeArgs where
    constructor MkNodeArgs
    curS : Nat
    totS : Nat
    {auto 0 curTotLTE : LTE curS totS}

public export
data Filename : Type where
    MkFilename : VectBits8 FilenameLength -> Filename
%runElab derive "Filename" [Show, Eq]

public export
Interpolation Filename where
    interpolate (MkFilename f) with (splitAt FilenameLengthName f)
        _ | (MkVectBits8Pair namev extv) =
            let name = rtrim "\{namev}"
                ext = rtrim "\{extv}"
            in if null ext then name else "\{name}.\{ext}"

namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> (fs : RootLabel) -> Type

namespace MaybeNode
    public export
    data MaybeNode : NodeCfg -> NodeArgs -> Presence -> Type where
        Nothing : MaybeNode cfg (MkNodeArgs 0 0 @{LTEZero}) Absent
        Just : Node cfg ar Rootless -> MaybeNode cfg ar Present

    public export
    maybe : b -> MaybeNode cfg ar pr -> (Node cfg ar Rootless -> b) -> b
    maybe x Nothing f = x
    maybe x (Just y) f = f y

namespace MaybeFilename
    public export
    data MaybeFilename : Presence -> Type where
        Nothing : MaybeFilename Absent
        Just : Filename -> MaybeFilename Present
    %runElab deriveIndexed "MaybeFilename" [Show, Eq]
    
namespace SnocVectNodeArgs
    public export
    data SnocVectNodeArgs : Nat -> Type where
        Lin : SnocVectNodeArgs 0
        (:<) : SnocVectNodeArgs k -> NodeArgs -> SnocVectNodeArgs (S k)

    public export
    totsum : SnocVectNodeArgs k -> Nat
    totsum [<] = 0
    totsum (xs :< (MkNodeArgs cur tot)) = tot + totsum xs

    public export
    totsumLTE : {tot : Nat} -> {0 ctprf : LTE cur tot} -> LTE tot $ totsum $ ars :< MkNodeArgs cur tot @{ctprf}
    totsumLTE = lteAddRight tot

namespace HSnocVectMaybeNode
    public export
    data HSnocVectMaybeNode : NodeCfg -> (k : Nat) -> SnocVectNodeArgs k -> SnocVectPresence k -> Type where
        Lin : HSnocVectMaybeNode cfg 0 [<] [<]
        (:<) : {ar : NodeArgs} ->
               HSnocVectMaybeNode cfg k ars prs ->
               MaybeNode cfg ar pr ->
               HSnocVectMaybeNode cfg (S k) (ars :< ar) (prs :< pr)

    public export
    traverse' : Applicative f =>
                (
                    {0 ar : NodeArgs} ->
                    {0 pr : Presence} ->
                    MaybeNode cfg ar pr ->
                    f (MaybeNode cfg ar pr)
                ) ->
                HSnocVectMaybeNode cfg k ars prs ->
                f (HSnocVectMaybeNode cfg k ars prs)
    traverse' g [<] = pure [<]
    traverse' g (xs :< x) = [| traverse' g xs :< g x |]

public export
data UniqNames : SnocVectPresence k -> Type

public export
data NameIsNew : UniqNames prs ->
                 MaybeFilename pr ->
                 Type

data UniqNames : SnocVectPresence k -> Type where
    Empty : UniqNames [<]
    NewName : (ff : UniqNames prs) -> (f : MaybeFilename pr) -> (0 _ : NameIsNew ff f) => UniqNames (prs :< pr)

data NameIsNew : UniqNames prs ->
                 MaybeFilename pr ->
                 Type where
    EmptyList : NameIsNew Empty f
    NewNothing : NameIsNew ff Nothing
    OldNothing : (0 sub : NameIsNew ff Nothing) => NameIsNew ff (Just newf) -> NameIsNew (NewName ff Nothing @{sub}) (Just newf)
    OldJust : (0 _ : So $ newf /= f) ->
              {0 ff : UniqNames prs} ->
              NameIsNew {prs} ff (Just newf) ->
              {0 sub : NameIsNew ff (Just f)} ->
              NameIsNew {prs=prs :< Present} (NewName ff (Just f) @{sub}) (Just newf)

-- TODO: Add upper bound of 268'435'445 clusters
namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> RootLabel -> Type where
        File : (0 clustNZ : IsSucc clustSize) =>
               (meta : Metadata) ->
               {k : Nat} ->
               SnocVectBits8 k ->
               Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize) @{Relation.reflexive}) Rootless
        Dir : forall clustSize.
              (0 clustNZ : IsSucc clustSize) =>
              (meta : Metadata) ->
              {k : Nat} ->
              {ars : SnocVectNodeArgs k} ->
              {prs : SnocVectPresence k} ->
              (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars prs) ->
              UniqNames prs ->
              Node (MkNodeCfg clustSize) (
                  MkNodeArgs (divCeilNZ (DirentSize * (2 + k)) clustSize) (divCeilNZ (DirentSize * (2 + k)) clustSize + totsum ars) @{lteAddRight (divCeilNZ (DirentSize * (2 + k)) clustSize) {m = totsum ars}}
              ) Rootless
        Root : forall clustSize.
               (0 clustNZ : IsSucc clustSize) =>
               {k : Nat} ->
               {ars : SnocVectNodeArgs k} ->
               {prs : SnocVectPresence k} ->
               (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars prs) ->
               UniqNames prs ->
               Node (MkNodeCfg clustSize) (
                   let cur' = divCeilNZ (DirentSize * k) clustSize
                   in MkNodeArgs cur' (cur' + totsum ars) @{lteAddRight cur' {m = totsum ars}}
               ) Rootful


public export
Filesystem : NodeCfg -> NodeArgs -> Type
Filesystem cfg ar = Node cfg ar Rootful




%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeCfg" [Show]
%runElab derive "Metadata" [Show]
%runElab derive "NodeArgs" [Show]
-- %runElab deriveIndexed "Blob" [Show]
%runElab deriveIndexed "SnocVectNodeArgs" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HSnocVectMaybeNode", "UniqNames"]

{-
Boot sector generation strategy:
BS_jmpBoot - random choice from a few options, see pdf;
BS_OEMNamme - MSWIN4.1 for max compat, randomly generate anything for max coverage (mkfs sets mkfs.fat here, so anything else should probably be fine);
BPB_BytsPerSec - 512 for max compat, random choice from 512, 1024, 2048, 4096 for max coverage (we should try this imo), used to compute clusterSize which is GIVEN;
BPB_SecPerClus - random choice from 1, 2, 4, 8, 16, 32, 64, 128, used to compute clusterSize which is GIVEN;
BPB_RsvdSecCnt - 32 for max compat, but could be practically anything non-zero? should be large enough to fit two (or more?) boot sectors and the FSInfo struct (would rather not touch this at first);
BPB_NumFATs - 2 for max compat, maybe try anything >= 1 for max coverage, but drivers are unlikely to support this (would not touch at first);
BPB_RootEntCnt - must be 0;
BPB_TotSec16 - must be 0;
BPB_Media - random choice from 0xF0, 0xF8-0xFF. don't forget to set the low byte of FAT[0] to the same value;
BPB_FATSz16 - must be 0;
BPB_SecPerTrk - irrelevant, picking 32 as a baseline, but this can be probably anything;
BPB_NumHeads - same as above, picking 8 as a baseline;
BPB_HiddSec - picking 0 here, not sure what would be valid here;
BPB_TotSec32 - this should be at least BPB_RsvdSecCnt + BPB_NumFATs * BPB_FATSz32 + maxClust * BPB_SecPerClus. note that maxClust is GENERATED, but must be >= 65525;
BPB_FATSz32 - this should be computed dynamically based on the GENERATED Filesystem object;
BPB_ExtFlags - see pdf, picking all 0s as a baseline, but disabling mirroring is definitely worth a try;
BPB_FSVer - must be 0;
BPB_RootClus - picking 2 as a baseline, but other values should be tried as well;
BPB_FSInfo - picking 1 as a baseline, other values should be tried as well, but make sure we are within the reserved area, keep in mind that a copy will exist in BackupBoot (not sure how to handle this properly);
BPB_BkBootSec - 6 for max compat, probably won't be trying other values;
BPB_Reserved - must be 0;
BS_DrvNum - irrelevant, picking 0x80 as a baseline, but could be anything probably;
BS_Reserved1 - must be 0;
BS_BootSig - must be 0x29;
BS_VolID - random;
BS_VolLab - random, make sure it is the same as in the root directory;
BS_FilSysType - must be "FAT32   ";
-}

-- NOTE: Don't forget that for the boot sector: sector[510] = 0x55, sector[511] = 0xAA

{-
FSI_LeadSig - must be 0x41615252;
FSI_Reserved1 - must be 0;
FSI_StrucSig - must be 0x61417272;
FSI_Free_Count - picking 0xFFFFFFFF at first (no data), then we should try computing it based on the GENERATED image. the pdf says it's "not necessarily correct", so putting in random values (within valid range) might actually be a good idea for testing;
FSI_Nxt_Free - picking 0xFFFFFFFF at first (no data), should try putting a random cluster number (within range) here;
FSI_Reserved2 - must be 0;
FSI_TrailSig - must be 0xAA550000;
-}

{-
pitfalls to keep in mind:
* all directories contain the . and .. entries (except the root directory)
* only certain characters are valid and 8.3 filenames. there's also weird stuff with spaces due to padding
* FAT mirroring can be on or off
* we should update FSInfo sometimes maybe
-}

-- TODO: Make a similar writeup for the FSInfo struct, plan out the image generation algorithm in detail
