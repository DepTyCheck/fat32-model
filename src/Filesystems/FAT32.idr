module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Order
import public Data.Nat.Order.Properties
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.Fuel
import public Deriving.DepTyCheck.Gen
import public Derive.Prelude
import Derive.Barbie
import Control.Barbie
import public Data.DPair
import public Data.ByteVect
import Data.Bits
import Data.Array.Core
import Data.Array.Indexed

%default total
%language ElabReflection

%hide Data.Array.Index.lsl
%hide Data.Nat.divCeilNZ

public export
divCeilNZ : Nat -> (y: Nat) -> (0 _ : IsSucc y) => Nat
divCeilNZ x y = case (modNatNZ x y %search) of
  Z   => divNatNZ x y %search
  S _ => S (divNatNZ x y %search)


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

namespace SnovVectNodeArgs
    public export
    data SnocVectNodeArgs : Nat -> Type where
        Lin : SnocVectNodeArgs 0
        (:<) : SnocVectNodeArgs k -> NodeArgs -> SnocVectNodeArgs (S k)

    public export
    totsum : SnocVectNodeArgs k -> Nat
    totsum [<] = 0
    totsum (xs :< (MkNodeArgs cur tot)) = tot + totsum xs

namespace HSnocVectMaybeNode
    public export
    data HSnocVectMaybeNode : NodeCfg -> (k : Nat) -> SnocVectNodeArgs k -> Bool -> Bool -> Type where
        Lin : HSnocVectMaybeNode cfg 0 [<] wb fs
        (:<) : HSnocVectMaybeNode cfg k ars wb fs ->
               MaybeNode cfg ar wb fs ->
               HSnocVectMaybeNode cfg (S k) (ars :< ar) wb fs

    public export
    data IndexIn : HSnocVectMaybeNode cfg k ars wb fs -> Type where
        Here : IndexIn (xs :< x)
        There : IndexIn xs -> IndexIn (xs :< x)

    public export
    traverse' : Applicative f =>
                (
                    {0 ar : NodeArgs} ->
                    MaybeNode cfg ar wb1 fs1 ->
                    f (MaybeNode cfg ar wb2 fs2)
                ) ->
                HSnocVectMaybeNode cfg k ars wb1 fs1 ->
                f (HSnocVectMaybeNode cfg k ars wb2 fs2)
    traverse' g [<] = pure [<]
    traverse' g (xs :< x) = [| traverse' g xs :< g x |]

namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> Bool -> Bool -> Type where
        File : (0 clustNZ : IsSucc clustSize) =>
               (meta : Metadata) ->
               {k : Nat} ->
               Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize)) False False
        FileB : (0 clustNZ : IsSucc clustSize) =>
                (meta : Metadata) ->
                {k : Nat} ->
                SnocVectBits8 k ->
                Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize)) True False
        Dir : forall k, ars, clustSize.
              (0 clustNZ : IsSucc clustSize) =>
              (meta : Metadata) ->
              (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb False) ->
              Node (MkNodeCfg clustSize) (
                  let cur' = divCeilNZ (DirentSize * (2 + k)) clustSize
                  in MkNodeArgs cur' (cur' + totsum ars) @{lteAddRight cur' {m = totsum ars}}
              ) wb False
        Root : forall k, ars, clustSize.
               (0 clustNZ : IsSucc clustSize) =>
               (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb False) ->
               Node (MkNodeCfg clustSize) (
                   let cur' = divCeilNZ (DirentSize * k) clustSize
                   in MkNodeArgs cur' (cur' + totsum ars) @{lteAddRight cur' {m = totsum ars}}
               ) wb True

namespace MaybeNode
    public export
    data IndexIn : MaybeNode cfg ar wb fs -> Type where
        Here : IndexIn $ Just node
        There : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs -> IndexIn $ Just $ Dir @{clustNZ} meta xs

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

boundedRange' : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => (fuel : Nat) -> List $ Subset Nat (`LT` b)
boundedRange' a b 0 = []
boundedRange' a b (S k) with (decomposeLte a b prf)
  boundedRange' a b (S k) | (Right peq) = []
  boundedRange' a b (S k) | (Left plt) with (boundedRange' (S a) b k)
    boundedRange' a b (S k) | (Left plt) | ps = (Element a plt) :: ps

public export
boundedRangeLT : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => List $ Subset Nat (`LT` b)
boundedRangeLT a b = boundedRange' a b (minus b a)

public export
boundedRangeLTE : (a : Nat) -> (b : Nat) -> (prf : LTE a b) => List $ Subset Nat (`LTE` b)
boundedRangeLTE a b= map (bimap id fromLteSucc) $ boundedRange' a (S b) (S $ minus b a) @{lteSuccRight prf}

genPaddedName : (padlen : Nat) -> LTE 1 padlen => Gen MaybeEmpty (VectBits8 padlen)
genPaddedName padlen = oneOf $ choiceMap (relax {ne=False} . alternativesOf . uncurry (genPaddedFilenameVect padlen)) (boundedRangeLTE 1 padlen)

public export
genFilename : Gen MaybeEmpty Filename
genFilename = pure $ MkFilename $ !(genPaddedName FilenameLengthName) ++ !(genPaddedName FilenameLengthExt)

namespace NameTree
    public export
    data NameTree : Node cfg ar wb fs -> Type

    public export
    data UniqNames : HSnocVectMaybeNode cfg k ars wb False -> Type

    public export
    data NameIsNew : (nodes : HSnocVectMaybeNode cfg k ars True False) -> UniqNames nodes -> Filename -> Type

    data NameTree : Node cfg ar wb fs -> Type where
        File : NameTree $ File @{clustNZ} meta
        FileB : NameTree $ FileB @{clustNZ} meta blob
        Dir : UniqNames nodes -> NameTree $ Dir @{clustNZ} meta nodes
        Root : UniqNames nodes -> NameTree $ Root @{clustNZ} nodes

    data UniqNames : HSnocVectMaybeNode cfg k ars wb False -> Type where
        Empty : UniqNames [<]
        NewName : (ff : UniqNames nodes) => (f : Filename) -> (0 _ : NameIsNew nodes ff f) => UniqNames (nodes :< node)

    data NameIsNew : (nodes : HSnocVectMaybeNode cfg k ars True False) -> UniqNames nodes -> Filename -> Type where
        E : NameIsNew [<] Empty f
        N : (0 _ : So $ x /= f) ->
            {0 ars : SnocVectNodeArgs k} ->
            {0 nodes : HSnocVectMaybeNode cfg k ars True False} ->
            {0 ff : UniqNames nodes} ->
            NameIsNew nodes ff x {k} {ars} ->
            {0 sub : NameIsNew nodes ff f {ars}} ->
            NameIsNew (nodes :< node) (NewName @{ff} f @{sub}) x

public export
genNameTree : Fuel ->
              (
                Fuel ->
                (cfg : NodeCfg) ->
                (wb : Bool) ->
                (fs : Bool) ->
                Gen MaybeEmpty (ar ** Node cfg ar wb fs)
              ) =>
              (Fuel -> Gen MaybeEmpty Bits8) =>
              (Fuel -> Gen MaybeEmpty Filename) =>
              (fs : Bool) ->
              (wb : Bool) ->
              (cfg : NodeCfg) ->
              Gen MaybeEmpty (ar ** node ** NameTree node {cfg} {ar} {wb} {fs})

interface ByteRepr a n | n where
    byteRepr : a -> ByteVect n

ByteRepr Bits8 1 where
    byteRepr x = singleton x

ByteRepr Bits16 2 where
    byteRepr n = pack $ cast <$> [ n .&. 0xff
                                 , n `shiftR` 8
                                 ]

ByteRepr Bits32 4 where
    byteRepr n = pack $ cast <$> [ n .&. 0xff
                                 , (n `shiftR` 8) .&. 0xff
                                 , (n `shiftR` 16) .&. 0xff
                                 , (n `shiftR` 24) .&. 0xff
                                 ]

ByteRepr Bits64 8 where
    byteRepr n = pack $ cast <$> [ n .&. 0xff
                                 , (n `shiftR` 8) .&. 0xff
                                 , (n `shiftR` 16) .&. 0xff
                                 , (n `shiftR` 24) .&. 0xff
                                 , (n `shiftR` 32) .&. 0xff
                                 , (n `shiftR` 40) .&. 0xff
                                 , (n `shiftR` 48) .&. 0xff
                                 , (n `shiftR` 56) .&. 0xff
                                 ]

record BootSectorData where
    constructor MkBootSectorData
    clustSize  : Nat
    dataClust  : Nat
    rootClust  : Nat
    bytsPerSec : Nat
    secPerClus : Nat
    rsvdSecCnt : Nat
    numFats    : Nat
    fatSz      : Nat
    activeFat  : Nat
    onlyOneFat : Bool

genBootSectorData : (clustSize : Nat) -> (dataClust : Nat) -> (rootClust : Nat) -> Gen MaybeEmpty BootSectorData
genBootSectorData clustSize dataClust rootClust = do
    let bytsPerSec : Nat
        bytsPerSec   = 512
    let secPerClus   = divNatNZ clustSize bytsPerSec %search
    let rsvdSecCnt   = 32
    let numFats      = 2
    let fatSz        = dataClust * 4 
    activeFat       <- elements' $ the (List Nat) $ map cast $ [0 .. (minus numFats 1)]
    onlyOneFat      <- elements' $ the (List _) [False, True]
    pure $ MkBootSectorData { clustSize
                            , dataClust
                            , rootClust
                            , bytsPerSec
                            , secPerClus
                            , rsvdSecCnt
                            , numFats
                            , fatSz
                            , activeFat
                            , onlyOneFat
                            }


record BootSector where
    constructor MkBootSector
    bs_jmpBoot     : ByteVect  3
    bs_OEMName     : ByteVect  8
    bpb_BytsPerSec : ByteVect  2
    bpb_SecPerClus : ByteVect  1
    bpb_RsvdSecCnt : ByteVect  2
    bpb_NumFATs    : ByteVect  1
    bpb_RootEntCnt : ByteVect  2
    bpb_TotSec16   : ByteVect  2
    bpb_Media      : ByteVect  1
    bpb_FATSz16    : ByteVect  2
    bpb_SecPerTrk  : ByteVect  2
    bpb_NumHeads   : ByteVect  2
    bpb_HiddSec    : ByteVect  4
    bpb_TotSec32   : ByteVect  4
    bpb_FATSz32    : ByteVect  4
    bpb_ExtFlags   : ByteVect  2
    bpb_FSVer      : ByteVect  2
    bpb_RootClus   : ByteVect  4
    bpb_FSInfo     : ByteVect  2
    bpb_BkBootSec  : ByteVect  2
    bpb_Reserved   : ByteVect 12
    bs_DrvNum      : ByteVect  1
    bs_Reserved1   : ByteVect  1
    bs_BootSig     : ByteVect  1
    bs_VolID       : ByteVect  4
    bs_VolLab      : ByteVect 11
    bs_FilSysType  : ByteVect  8

-- %runElab derive "BootSector" [Barbie]

genBootSector : BootSectorData -> Gen MaybeEmpty BootSector
genBootSector bsdata = do
    bs_jmpBoot         <- oneOf $ alternativesOf (do pure $ pack [0xEB, !genBits8, 0x90])
                            ++ alternativesOf (do pure $ pack [0xE9, !genBits8, !genBits8])
    bs_OEMName         <- packVect <$> genVectBits8 _
    -- TODO: generate powers of 2 from 512 to clustSize
    let bpb_BytsPerSec  = byteRepr $ cast bsdata.bytsPerSec
    let bpb_SecPerClus  = byteRepr $ cast $ bsdata.secPerClus
    -- TODO: maybe add some sectors for fun here
    let bpb_RsvdSecCnt  = byteRepr $ cast bsdata.rsvdSecCnt
    -- TODO: generate from 1 to 8 FATs
    let bpb_NumFATs     = byteRepr $ cast bsdata.numFats
    let bpb_RootEntCnt  = byteRepr 0
    let bpb_TotSec16    = byteRepr 0
    bpb_Media          <- elements' $ byteRepr <$> 
                          the (List _) [0xF0, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF]
    let bpb_FATSz16     = byteRepr 0
    bpb_SecPerTrk      <- packVect <$> genVectBits8 _
    bpb_NumHeads       <- packVect <$> genVectBits8 _
    let bpb_HiddSec     = byteRepr 0
    let tFATSz32        = bsdata.dataClust * 4 
    let bpb_TotSec32    = byteRepr $ cast $ bsdata.rsvdSecCnt + bsdata.numFats * bsdata.fatSz + bsdata.dataClust * bsdata.secPerClus
    let bpb_FATSz32     = byteRepr $ cast bsdata.fatSz
    -- TODO: generate mirroring and stuff
    let bpb_ExtFlags    = byteRepr $ cast bsdata.activeFat .|. (the Bits16 (if bsdata.onlyOneFat then 1 else 0) `shiftL` 7)
    let bpb_FSVer       = byteRepr 0
    let bpb_RootClus    = byteRepr $ cast bsdata.rootClust
    let bpb_FSInfo      = byteRepr 1
    let bpb_BkBootSec   = byteRepr 6
    let bpb_Reserved    = replicate _ 0
    let bs_DrvNum       = byteRepr 0x80
    let bs_Reserved1    = replicate _ 0
    let bs_BootSig      = byteRepr 0x29
    bs_VolID           <- packVect <$> genVectBits8 _
    bs_VolLab          <- packVect <$> genVectBits8 _
    let bs_FilSysType   = pack $ map cast ['F', 'A', 'T', '3', '2', ' ', ' ', ' ']
    pure $ MkBootSector { bs_jmpBoot
                        , bs_OEMName
                        , bpb_BytsPerSec
                        , bpb_SecPerClus
                        , bpb_RsvdSecCnt
                        , bpb_NumFATs
                        , bpb_RootEntCnt
                        , bpb_TotSec16
                        , bpb_Media
                        , bpb_FATSz16
                        , bpb_SecPerTrk
                        , bpb_NumHeads
                        , bpb_HiddSec
                        , bpb_TotSec32
                        , bpb_FATSz32
                        , bpb_ExtFlags
                        , bpb_FSVer
                        , bpb_RootClus
                        , bpb_FSInfo
                        , bpb_BkBootSec
                        , bpb_Reserved
                        , bs_DrvNum
                        , bs_Reserved1
                        , bs_BootSig
                        , bs_VolID
                        , bs_VolLab
                        , bs_FilSysType
                        }



record FSInfo where
    constructor MkFSInfo
    fsi_LeadSig    : ByteVect   4
    fsi_Reserved1  : ByteVect 480
    fsi_StrucSig   : ByteVect   4
    fsi_Free_Count : ByteVect   4
    fsi_Nxt_Free   : ByteVect   4
    fsi_Reserved2  : ByteVect  12
    fsi_TrailSig   : ByteVect   4

fsInfoGen : (dataClust : Nat) -> Gen MaybeEmpty FSInfo
fsInfoGen dataClust = do
  let fsi_LeadSig   = byteRepr 0x41615252
  let fsi_Reserved1 = replicate _ 0
  let fsi_StrucSig  = byteRepr 0x61417272
  fsi_Free_Count   <- elements' $ the (List _) $ map (byteRepr . cast) $ [0 .. dataClust]
  fsi_Nxt_Free     <- elements' $ the (List _) $ map (byteRepr . cast) $ [0 .. (minus dataClust 1)]
  let fsi_Reserved2 = replicate _ 0
  let fsi_TrailSig  = byteRepr 0xAA550000
  pure $ MkFSInfo { fsi_LeadSig
                  , fsi_Reserved1
                  , fsi_StrucSig
                  , fsi_Free_Count
                  , fsi_Nxt_Free
                  , fsi_Reserved2
                  , fsi_TrailSig
                  }

%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeCfg" [Show]
%runElab derive "Metadata" [Show]
%runElab derive "NodeArgs" [Show]
%runElab deriveIndexed "SnocVectNodeArgs" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HSnocVectMaybeNode"]
-- %runElab deriveIndexed "Filesystem" [Show]

-- serializeNode : {clustSize : Nat} -> (0 clustNZ : IsSucc clustSize) => (node : Node (MkNodeCfg clustSize) (MkNodeArgs cur tot) True fs) -> NameTree node -> IArray tot (Fin m) -> ByteVect (cur * clustSize)
-- serializeNode (FileB meta x) names cmap = packVect $ padBlob clustSize clustNZ x
-- serializeNode (Dir meta entries) names cmap = ?serializeNode_rhs_2
-- serializeNode (Root entries) names cmap = ?serializeNode_rhs_3

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
