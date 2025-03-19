module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.Fuel
import public Deriving.DepTyCheck.Gen
import public Derive.Prelude
import public Data.DPair

%default total


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
    FilenameLength : Nat
    FilenameLength = 11

    public export
    FilenameLengthExtless : Nat
    FilenameLengthExtless = 8

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

namespace Node
    public export
    data Node : NodeCfg -> NodeArgs -> Bool -> Bool -> Type where
        File : (0 clustNZ : IsSucc clustSize) =>
               (meta : Metadata) ->
               Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize)) False False
        FileB : (0 clustNZ : IsSucc clustSize) =>
                (meta : Metadata) ->
                VectBits8 k ->
                Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize)) True False
        Dir : (0 clustNZ : IsSucc clustSize) =>
              (meta : Metadata) ->
              (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb False) ->
              Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ (DirentSize * (2 + k)) clustSize) (divCeilNZ (DirentSize * (2 + k)) clustSize + totsum ars)) wb False
        Root : (0 clustNZ : IsSucc clustSize) =>
               (entries : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars wb False) ->
               Node (MkNodeCfg clustSize) (MkNodeArgs (divCeilNZ (DirentSize * k) clustSize) (divCeilNZ (DirentSize * k) clustSize + totsum ars)) wb True

namespace MaybeNode
    public export
    data IndexIn : MaybeNode cfg ar wb fs -> Type where
        Here : IndexIn $ Just node
        There : IndexIn {cfg = MkNodeCfg clustSize @{clustNZ}} xs -> IndexIn $ Just $ Dir @{clustNZ} meta xs

public export
Filesystem : NodeCfg -> {cur : Nat} -> (tot : Nat) -> Bool -> Type
Filesystem cfg tot wb = Node cfg (MkNodeArgs cur tot) wb True

public export
FilesystemB : NodeCfg -> {cur : Nat} -> (tot : Nat) -> Type
FilesystemB cfg tot = Node cfg (MkNodeArgs cur tot) True True

public export %hint
genBits8 : Gen MaybeEmpty Bits8
genBits8 = elements' $ the (List Bits8) [0..255]

public export
genNode : Fuel -> (Fuel -> Gen MaybeEmpty Bits8) => (cfg : NodeCfg) -> (withBlob : Bool) -> (fs : Bool) -> Gen MaybeEmpty (ar ** Node cfg ar withBlob fs)

public export
genFilesystem : Fuel -> (cfg : NodeCfg) -> Gen MaybeEmpty (cur ** tot ** Filesystem cfg {cur} tot False)
genFilesystem fuel cfg = do
    ((MkNodeArgs cur tot) ** res) <- genNode fuel cfg False True
    pure (cur ** tot ** res)

public export
Filename : Type
Filename = VectBits8 FilenameLength


-- TODO: Correct filenames to be 8.3 compliant
-- public export
-- data NodeB : Maybe (Node' cfg ar) -> Type where
--     NothingB : NodeB Nothing
--     FileB : (0 clustNZ : IsSucc clustSize) =>
--             Filename ->
--             Vect k Bits8 -> 
--             NodeB {cfg = (MkNodeCfg clustSize)} {ar = MkNodeArgs (divCeilNZ k clustSize) (divCeilNZ k clustSize)} (Just $ File' meta {k})
--     DirB : (0 clustNZ : IsSucc clustSize) =>
--            {ents : HVectMaybeNode' (MkNodeCfg clustSize) k ars} ->
--            Filename ->
--            -- assert_total is correct because All2 is a Functor
--            (nodes : All2 (assert_total NodeB) ents) ->
--            NodeB (Just $ Dir' meta ents {clustSize})
--
-- public export
-- data FilesystemB : Filesystem' cfg sz -> Type where
--     RootB : (0 clustNZ : IsSucc clustSize) =>
--             {0 ents : HVectMaybeNode' (MkNodeCfg clustSize) k ars} ->
--             (nodes : All2 NodeB ents) ->
--             FilesystemB (Root' ents)

public export
genVectBits8 : (n : Nat) -> Gen NonEmpty (VectBits8 n)
genVectBits8 Z = pure []
genVectBits8 (S k) = [| chooseAny :: genVectBits8 k |]

genValidFilenameChar : Gen NonEmpty Bits8
genValidFilenameChar = elements $ fromList $ map cast $ the (List Char) $ ['A'..'Z'] ++ ['0'..'9'] ++ unpack "!#$%&'()-@^_`{}~"

genValidFilenameChars : (len : Nat) -> Gen NonEmpty (VectBits8 len)
genValidFilenameChars Z = pure []
genValidFilenameChars (S k) = [| genValidFilenameChar :: genValidFilenameChars k |]

genPaddedFilenameVect : (len : Nat) -> (padlen : Nat) -> (0 prf : LTE len padlen) => Gen NonEmpty (VectBits8 padlen)
genPaddedFilenameVect len padlen = rewrite (sym $ plusMinusLte len padlen prf) in rewrite (plusCommutative (minus padlen len) len) in flip (++) (fromVect $ replicate (minus padlen len) (cast ' ')) <$> genValidFilenameChars len

public export
genFilename : Gen NonEmpty Filename
-- TODO: implement

isJustSpaces : VectBits8 k -> Bool
isJustSpaces [] = True
isJustSpaces (x :: xs) = (cast x == ' ') && (isJustSpaces xs)

isValidFilenamePart : VectBits8 k -> Bool
isValidFilenamePart [] = True
isValidFilenamePart (x :: xs) with (the Char $ cast x)
  isValidFilenamePart (x :: xs) | ' ' = isJustSpaces xs
  isValidFilenamePart (x :: xs) | c   = (('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || (elem c $ unpack "!#$%&'()-@^_`{}~")) && isValidFilenamePart xs

public export
isValidFilename : Filename -> Bool
isValidFilename x with (splitAt FilenameLengthExtless x)
  isValidFilename x | (MkVectBits8Pair nam ext) = isValidFilenamePart nam && isValidFilenamePart ext

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
genNameTree : Fuel -> (fs : Bool) -> (wb : Bool) -> (ar : NodeArgs) -> (cfg : NodeCfg) -> (node : Node cfg ar wb fs) -> Gen MaybeEmpty (NameTree node)

-- public export
-- genMaybeNodeB : {cfg : NodeCfg} -> 
--                 (node : MaybeNode cfg cur tot) -> 
--                 Gen NonEmpty (MaybeNodeB node)
-- genMaybeNodeB Nothing = pure Nothing
-- genMaybeNodeB (Just $ File meta {k}) = do
--     name <- genVectBits8 FilenameLength
--     content <- genVectBits8 k
--     pure $ Just $ FileB name content
-- genMaybeNodeB (Just $ Dir meta entries) = do
--     name <- genVectBits8 FilenameLength
--     ents <- assert_total $ traverse genMaybeNodeB entries
--     pure $ Just $ DirB name ents
--
-- public export
-- genFilesystemB : {cfg : NodeCfg} -> 
--                  (fs : Filesystem cfg sz) -> 
--                  Gen NonEmpty (FilesystemB fs)
-- genFilesystemB (Root entries) = RootB <$> traverse genMaybeNodeB entries


%language ElabReflection
%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeCfg" [Show]
%runElab derive "Metadata" [Show]
%runElab derive "NodeArgs" [Show]
%runElab deriveIndexed "SnocVectNodeArgs" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HSnocVectMaybeNode"]
-- %runElab deriveIndexed "Filesystem" [Show]

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
