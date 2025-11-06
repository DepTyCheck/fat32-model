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

namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> (wb : Bool) -> (fs : Bool) -> Type

namespace MaybeNode
    public export
    data MaybeNode : NodeCfg -> NodeArgs -> Bool -> Bool -> Type where
        Nothing : MaybeNode cfg ar wb fs
        Just : Node cfg ar wb fs -> MaybeNode cfg ar wb fs

    public export
    maybe : b -> MaybeNode cfg ar wb fs -> (Node cfg ar wb fs -> b) -> b
    maybe x Nothing f = x
    maybe x (Just y) f = f y
    
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
    data HSnocVectMaybeNode : NodeCfg -> (k : Nat) -> SnocVectNodeArgs k -> Bool -> Type where
        Lin : HSnocVectMaybeNode cfg 0 [<] wb
        (:<) : {ar : NodeArgs} ->
               HSnocVectMaybeNode cfg k ars wb ->
               MaybeNode cfg ar wb False ->
               HSnocVectMaybeNode cfg (S k) (ars :< ar) wb

    public export
    traverse' : Applicative f =>
                (
                    {0 ar : NodeArgs} ->
                    MaybeNode cfg ar wb1 False ->
                    f (MaybeNode cfg ar wb2 False)
                ) ->
                HSnocVectMaybeNode cfg k ars wb1 ->
                f (HSnocVectMaybeNode cfg k ars wb2)
    traverse' g [<] = pure [<]
    traverse' g (xs :< x) = [| traverse' g xs :< g x |]

-- TODO: Add upper bound of 268'435'445 clusters
namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> Bool -> Bool -> Type where
        File : (0 clustNZ : IsSucc clustSize) =>
               (meta : Metadata) ->
               {k : Nat} ->
               Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize) @{Relation.reflexive}) False False
        FileB : (0 clustNZ : IsSucc clustSize) =>
                (meta : Metadata) ->
                {k : Nat} ->
                SnocVectBits8 k ->
                Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize) @{Relation.reflexive}) True False
        Dir : forall clustSize.
              (0 clustNZ : IsSucc clustSize) =>
              (meta : Metadata) ->
              {k : Nat} ->
              {ars : SnocVectNodeArgs k} ->
              (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb) ->
              Node (MkNodeCfg clustSize) (
                  MkNodeArgs (divCeilNZ (DirentSize * (2 + k)) clustSize) (divCeilNZ (DirentSize * (2 + k)) clustSize + totsum ars) @{lteAddRight (divCeilNZ (DirentSize * (2 + k)) clustSize) {m = totsum ars}}
              ) wb False
        Root : forall clustSize.
               (0 clustNZ : IsSucc clustSize) =>
               {k : Nat} ->
               {ars : SnocVectNodeArgs k} ->
               (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb) ->
               Node (MkNodeCfg clustSize) (
                   let cur' = divCeilNZ (DirentSize * k) clustSize
                   in MkNodeArgs cur' (cur' + totsum ars) @{lteAddRight cur' {m = totsum ars}}
               ) wb True


public export
Filesystem : NodeCfg -> NodeArgs -> Type
Filesystem cfg ar = Node cfg ar False True

public export
FilesystemB : NodeCfg -> NodeArgs -> Type
FilesystemB cfg ar = Node cfg ar True True

public export
genNode : Fuel -> (Fuel -> Gen MaybeEmpty Bits8) => (cfg : NodeCfg) -> (withBlob : Bool) -> (fs : Bool) -> Gen MaybeEmpty (ar ** Node cfg ar withBlob fs)

public export
genFilesystem : Fuel -> (cfg : NodeCfg) -> Gen MaybeEmpty (ar ** Filesystem cfg ar)
genFilesystem fuel cfg = genNode fuel cfg False True

fillBlobs' : MaybeNode cfg ar False False -> Gen MaybeEmpty $ MaybeNode cfg ar True False
fillBlobs' Nothing = pure Nothing
fillBlobs' (Just $ Dir meta entries) = Just <$> Dir meta <$> assert_total (traverse' fillBlobs' entries)
fillBlobs' (Just $ File meta {k}) = Just <$> FileB meta <$> genSnocVectBits8 k

fillBlobs : Node cfg ar False True -> Gen MaybeEmpty $ Node cfg ar True True
fillBlobs (Root entries) = Root <$> (traverse' fillBlobs' entries)

public export
genFilesystemB : Fuel -> (cfg : NodeCfg) -> Gen MaybeEmpty (ar ** FilesystemB cfg ar)
genFilesystemB fuel cfg = do
    (ar ** fsr) <- genFilesystem fuel cfg
    fsb <- fillBlobs fsr
    pure (ar ** fsb)

public export
data Filename : Type where
    MkFilename : VectBits8 FilenameLength -> Filename
%runElab derive "Filename" [Show, Eq]

genValidFilenameChar : Gen MaybeEmpty Bits8
genValidFilenameChar = elements' $ map cast $ the (List Char) $ ['A'..'Z'] ++ ['0'..'9'] ++ unpack "!#$%&'()-@^_`{}~"

genValidFilenameChars : (len : Nat) -> Gen MaybeEmpty (VectBits8 len)
genValidFilenameChars Z = pure []
genValidFilenameChars (S k) = [| genValidFilenameChar :: genValidFilenameChars k |]

genPaddedFilenameVect : (padlen : Nat) -> (len : Nat) -> (0 prf : LTE len padlen) -> Gen MaybeEmpty (VectBits8 padlen)
genPaddedFilenameVect padlen len prf = rewrite sym $ plusMinusLte len padlen prf in
                                   rewrite plusCommutative (minus padlen len) len in
                                   flip (++) (fromVect $ replicate (minus padlen len) $ cast ' ') <$> genValidFilenameChars len

genPaddedName : (lo : Nat) -> (hi : Nat) -> LTE lo hi => Gen MaybeEmpty (VectBits8 hi)
genPaddedName lo hi = do
    Element clen prf <- elements $ fromList $ boundedRangeLTE lo hi
    genPaddedFilenameVect hi clen prf

public export
genFilename : Gen MaybeEmpty Filename
genFilename = pure $ MkFilename $ !(genPaddedName 1 FilenameLengthName) ++ !(genPaddedName 0 FilenameLengthExt)


%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeCfg" [Show]
%runElab derive "Metadata" [Show]
%runElab derive "NodeArgs" [Show]
%runElab deriveIndexed "SnocVectNodeArgs" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HSnocVectMaybeNode"]

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
