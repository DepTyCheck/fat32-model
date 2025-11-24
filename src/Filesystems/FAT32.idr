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
data BlobLabel = Blobful | Blobless

public export
data RootLabel = Rootful | Rootless

public export
data Blob : (k : Nat) -> (label : BlobLabel) -> Type where
    BlobNone : Blob k Blobless
    BlobSome : SnocVectBits8 k -> Blob k Blobful

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
            let name = (reverse . ltrim . reverse) "\{namev}"
                ext = (reverse . ltrim . reverse) "\{extv}"
            in if null ext then name else "\{name}.\{ext}"
            
public export
data UniqNames : Nat -> Type

public export
data NameIsNew : (k : Nat) -> UniqNames k -> Filename -> Type

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
data NameLabel = Nameful | Nameless

public export
data Names : (k : Nat) -> (label : NameLabel) -> Type where
    NamesNone : Names k Nameless
    NamesSome : UniqNames k -> Names k Nameful

namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> (wb : BlobLabel) -> (nm : NameLabel) -> (fs : RootLabel) -> Type

namespace MaybeNode
    public export
    data MaybeNode : NodeCfg -> NodeArgs -> BlobLabel -> NameLabel -> RootLabel -> Type where
        Nothing : MaybeNode cfg ar wb nm fs
        Just : Node cfg ar wb nm fs -> MaybeNode cfg ar wb nm fs

    public export
    maybe : b -> MaybeNode cfg ar wb nm fs -> (Node cfg ar wb nm fs -> b) -> b
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
    data HSnocVectMaybeNode : NodeCfg -> (k : Nat) -> SnocVectNodeArgs k -> BlobLabel -> NameLabel -> Type where
        Lin : HSnocVectMaybeNode cfg 0 [<] wb nm
        (:<) : {ar : NodeArgs} ->
               HSnocVectMaybeNode cfg k ars wb nm ->
               MaybeNode cfg ar wb nm Rootless ->
               HSnocVectMaybeNode cfg (S k) (ars :< ar) wb nm

    public export
    traverse' : Applicative f =>
                (
                    {0 ar : NodeArgs} ->
                    MaybeNode cfg ar wb1 nm1 Rootless ->
                    f (MaybeNode cfg ar wb2 nm2 Rootless)
                ) ->
                HSnocVectMaybeNode cfg k ars wb1 nm1 ->
                f (HSnocVectMaybeNode cfg k ars wb2 nm2)
    traverse' g [<] = pure [<]
    traverse' g (xs :< x) = [| traverse' g xs :< g x |]

-- TODO: Add upper bound of 268'435'445 clusters
namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> BlobLabel -> NameLabel -> RootLabel -> Type where
        File : (0 clustNZ : IsSucc clustSize) =>
               (meta : Metadata) ->
               {k : Nat} ->
               Blob k wb ->
               Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize) @{Relation.reflexive}) wb nm Rootless
        Dir : forall clustSize.
              (0 clustNZ : IsSucc clustSize) =>
              (meta : Metadata) ->
              {k : Nat} ->
              {ars : SnocVectNodeArgs k} ->
              Names k nm ->
              (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb nm) ->
              Node (MkNodeCfg clustSize) (
                  MkNodeArgs (divCeilNZ (DirentSize * (2 + k)) clustSize) (divCeilNZ (DirentSize * (2 + k)) clustSize + totsum ars) @{lteAddRight (divCeilNZ (DirentSize * (2 + k)) clustSize) {m = totsum ars}}
              ) wb nm Rootless
        Root : forall clustSize.
               (0 clustNZ : IsSucc clustSize) =>
               {k : Nat} ->
               {ars : SnocVectNodeArgs k} ->
               Names k nm ->
               (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb nm) ->
               Node (MkNodeCfg clustSize) (
                   let cur' = divCeilNZ (DirentSize * k) clustSize
                   in MkNodeArgs cur' (cur' + totsum ars) @{lteAddRight cur' {m = totsum ars}}
               ) wb nm Rootful


public export
Filesystem : NodeCfg -> NodeArgs -> Type
Filesystem cfg ar = Node cfg ar Blobless Nameless Rootful

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

public export %hint
genFilename : Gen MaybeEmpty Filename
genFilename = pure $ MkFilename $ !(genPaddedName 1 FilenameLengthName) ++ !(genPaddedName 0 FilenameLengthExt)

public export
genUniqNames : Fuel ->
               (Fuel -> Gen MaybeEmpty Bits8) =>
               (Fuel -> Gen MaybeEmpty Filename) =>
               (k : Nat) ->
               Gen MaybeEmpty $ UniqNames k

public export
genNode : Fuel -> 
          (Fuel -> Gen MaybeEmpty Bits8) => 
          (Fuel -> (k : Nat) -> Gen MaybeEmpty (UniqNames k)) =>
          (cfg : NodeCfg) -> 
          (withBlob : BlobLabel) -> 
          (nm : NameLabel) -> 
          (fs : RootLabel) -> 
          Gen MaybeEmpty (ar ** Node cfg ar withBlob nm fs)

public export
genFilesystem : Fuel -> (cfg : NodeCfg) -> Gen MaybeEmpty (ar ** Filesystem cfg ar)
genFilesystem fuel cfg = genNode fuel @{%search} @{\f => genUniqNames f} cfg Blobless Nameless Rootful

fillBlobs' : MaybeNode cfg ar Blobless nm Rootless -> Gen MaybeEmpty $ MaybeNode cfg ar Blobful nm Rootless
fillBlobs' Nothing = pure Nothing
fillBlobs' (Just $ Dir meta names entries) = Just <$> Dir meta names <$> assert_total (traverse' fillBlobs' entries)
fillBlobs' (Just $ File meta _ {k}) = Just <$> File meta <$> BlobSome <$> genSnocVectBits8 k

public export
fillBlobs : Node cfg ar Blobless nm Rootful -> Gen MaybeEmpty $ Node cfg ar Blobful nm Rootful
fillBlobs (Root names entries) = Root names <$> (traverse' fillBlobs' entries)


fillNames' : Fuel -> 
             MaybeNode cfg ar wb Nameless Rootless -> 
             Gen MaybeEmpty $ MaybeNode cfg ar wb Nameful Rootless
fillNames' _ Nothing = pure Nothing
fillNames' _ (Just (File meta x)) = pure $ Just $ File meta x
fillNames' fuel (Just (Dir meta _ entries {k})) = pure $ Just $ Dir meta (NamesSome !(genUniqNames fuel k)) !(assert_total $ traverse' (fillNames' fuel) entries)

public export
fillNames : Fuel -> 
            Node cfg ar wb Nameless Rootful -> 
            Gen MaybeEmpty $ Node cfg ar wb Nameful Rootful
fillNames fuel (Root _ entries {k}) = pure $ Root (NamesSome !(genUniqNames fuel k)) !(traverse' (fillNames' fuel) entries) 



%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeCfg" [Show]
%runElab derive "Metadata" [Show]
%runElab derive "NodeArgs" [Show]
%runElab deriveIndexed "Blob" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["UniqNames", "Names"]
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
