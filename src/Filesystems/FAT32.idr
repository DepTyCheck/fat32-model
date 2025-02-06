module Filesystems.FAT32

import public Data.Nat
import public Data.Nat.Division
import public Data.Monomorphic.Vect
import public Data.FinInc
import public Data.Fuel
import public Deriving.DepTyCheck.Gen
import public Derive.Prelude

%default total

namespace Constants
    public export
    DirentSize : Nat
    DirentSize = 32

    public export
    FilenameLength : Nat
    FilenameLength = 11

public export
record NodeParams where
    constructor MkNodeParams
    clusterSize : Nat        -- bytes per cluster
-- NOTE: clusterSize must not be greater than 32K
    {auto 0 clusterSizeNZ : IsSucc clusterSize}

public export
record Metadata where
    constructor MkMetadata
    readOnly : Bool
    hidden : Bool
    system : Bool
    archive : Bool

public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type

namespace MaybeNode
    public export
    data MaybeNode : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
        Nothing : MaybeNode cfg n m cur tot
        Just : Node cfg n m tot cur -> MaybeNode cfg n m tot cur

public export
data NodeArgs : Type where
    MkNodeArgs : (n : Nat) -> (m : Nat) -> (cur : FinInc n) -> (tot : FinInc m) -> NodeArgs

namespace VectNodeArgs
    public export
    data VectNodeArgs : Nat -> Type where
        Nil : VectNodeArgs 0
        (::) : NodeArgs -> VectNodeArgs k -> VectNodeArgs (S k)

namespace HVectMaybeNode
    public export
    data HVectMaybeNode : NodeParams -> (k : Nat) -> (ns : VectNat k) -> (ms : VectNat k) -> HVectFinInc k ns -> HVectFinInc k ms -> Type where
        Nil : HVectMaybeNode cfg 0 [] [] [] []
        (::) : forall cfg, n, cur, ns, m, ms, cs, ts, tot.
               MaybeNode cfg n m cur tot -> 
               HVectMaybeNode cfg k ns ms cs ts -> 
               HVectMaybeNode cfg (S k) (n :: ns) (m :: ms) (cur :: cs) (tot :: ts)

namespace HVectMaybeNode''
    public export
    data HVectMaybeNode'' : NodeParams -> (k : Nat) -> VectNodeArgs k -> Type where
        Nil : HVectMaybeNode'' cfg 0 []
        (::) : forall cfg.
               {n : _} ->
               {cur : _} ->
               forall ns, m, ms, cs, ts, tot.
               MaybeNode cfg n m cur tot -> 
               HVectMaybeNode'' cfg k nargs -> 
               HVectMaybeNode'' cfg (S k) ((MkNodeArgs n m cur tot) :: nargs)

public export
HVectMaybeNode' : NodeParams -> (k : Nat) -> Vect k NodeArgs -> Type
HVectMaybeNode' cfg k nargs = All (\(MkNodeArgs n m cur tot) => Maybe (Node cfg n m cur tot)) nargs

public export
data Node : NodeParams -> (n : Nat) -> (m : Nat) -> FinInc n -> FinInc m -> Type where
    File : (0 clustNZ : IsSucc clustSize) =>
           {k : FinInc (n * clustSize)} ->
           (meta : Metadata) ->
           Node (MkNodeParams clustSize) n n (divCeilFlip clustSize k) (divCeilFlip clustSize k)
-- NOTE: kv is the number of dirents *excluding* the additional . and .. entries. (2 + kv) in the kp condition accounts for this
    Dir : forall clustSize, n.
          {kv : _} ->
          forall ns, ms, cs, ts.
          (0 clustNZ : IsSucc clustSize) =>
          {kp : LTE (2 + kv) (divNatNZ (n * clustSize) DirentSize %search)} ->
          (meta : Metadata) ->
          (entries : HVectMaybeNode (MkNodeParams clustSize) kv ns ms cs ts) ->
          Node (MkNodeParams clustSize) n (n + sum ms) 
                                            (divCeilFlipWeak clustSize 
                                            @{clustNZ} 
                                            (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * (MkFinInc (2 + kv) kp))
                                            {r = modNatNZ (n * clustSize) DirentSize %search}) 
                                            ((divCeilFlipWeak clustSize 
                                            @{clustNZ} 
                                            (rewrite numerMinusModIsDenomMultQuot (n * clustSize) DirentSize in DirentSize * (MkFinInc (2 + kv) kp)) {n}
                                            {r = modNatNZ (n * clustSize) DirentSize %search}) + sum ts)

public export
data Filesystem : NodeParams -> Nat -> Type where
    Root : (0 clustNZ : IsSucc clustSize) =>
           {0 klte : LTE k (divNatNZ (n * clustSize) DirentSize %search)} ->
           (entries : HVectMaybeNode (MkNodeParams clustSize) k ns ms cs ts) ->
           Filesystem (MkNodeParams clustSize) (n + sum ms)

public export
genFilesystem : Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust)

public export
Filename : Type
Filename = VectBits8 FilenameLength

public export
data NodeB : {0 c : FinInc n} -> {0 t : FinInc m} -> Node cfg n m c t -> Type

namespace MaybeNodeB
    public export
    data MaybeNodeB : {0 c : FinInc n} -> {0 t : FinInc m} -> MaybeNode cfg n m c t -> Type where
        Nothing : MaybeNodeB Nothing
        Just : NodeB node -> MaybeNodeB (Just node)

namespace HVectMaybeNodeB
    public export
    data HVectMaybeNodeB : (cfg : NodeParams) -> (k : Nat) -> {0 ns : VectNat k} -> {0 ms : VectNat k} -> {0 cs : HVectFinInc k ns} -> {0 ts : HVectFinInc k ms} -> HVectMaybeNode cfg k ns ms cs ts -> Type where
        Nil : HVectMaybeNodeB cfg 0 []
        (::) : {0 n : _} ->
               {0 cur : _} ->
               {0 ns : VectNat k} ->
               {0 ms : VectNat k} ->
               {0 cs : HVectFinInc k ns} ->
               {0 ts : HVectFinInc k ms} ->
               {0 node : MaybeNode cfg n m cur t} ->
               {0 nodes : HVectMaybeNode cfg k ns ms cs ts} ->
               MaybeNodeB node -> 
               HVectMaybeNodeB cfg k nodes -> 
               HVectMaybeNodeB cfg (S k) (node :: nodes)
    
    public export
    traverse : Applicative f => 
               (
                   {0 n : Nat} -> 
                   {0 m : Nat} -> 
                   {0 cur : FinInc n} -> 
                   {0 tot : FinInc m} -> 
                   (node : MaybeNode cfg n m cur tot) -> 
                   f (MaybeNodeB node)
                ) -> 
                (nodes : HVectMaybeNode cfg k ns ms cs ts) -> 
                f (HVectMaybeNodeB cfg k nodes)
    traverse g [] = pure []
    traverse g (x :: xs) = [| g x :: traverse g xs |]

-- TODO: Correct filenames to be 8.3 compliant
public export
data NodeB : {0 cur : FinInc n} -> {0 tot : FinInc m} -> Node cfg n m cur tot -> Type where
    FileB : (0 clustNZ : IsSucc clustSize) =>
            Filename ->
            {0 k : FinInc (n * clustSize)} ->
            VectBits8 k.val -> 
            NodeB {n} {cfg = (MkNodeParams clustSize)} {cur = divCeilFlip clustSize k} {tot = divCeilFlip clustSize k} (File meta {k})
    DirB : (0 clustNZ : IsSucc clustSize) =>
           {ents : HVectMaybeNode (MkNodeParams clustSize) kv ns ms cs ts} ->
           Filename ->
           (nodes : HVectMaybeNodeB (MkNodeParams clustSize) kv ents) ->
           NodeB (Dir meta ents {n})

public export
data FilesystemB : Filesystem cfg sz -> Type where
    RootB : (0 clustNZ : IsSucc clustSize) =>
            {0 ents : HVectMaybeNode (MkNodeParams clustSize) k ns ms cs ts} ->
            (nodes : HVectMaybeNodeB (MkNodeParams clustSize) k ents) ->
            FilesystemB (Root ents {n})

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

public export
genMaybeNodeB : {cfg : NodeParams} -> 
                {0 n : Nat} -> 
                {0 cur : FinInc n} -> 
                (node : MaybeNode cfg n m cur tot) -> 
                Gen NonEmpty (MaybeNodeB node)
genMaybeNodeB Nothing = pure Nothing
genMaybeNodeB (Just $ File meta {k}) = do
    name <- genVectBits8 FilenameLength
    content <- genVectBits8 k.val
    pure $ Just $ FileB name content
genMaybeNodeB (Just $ Dir meta entries) = do
    name <- genVectBits8 FilenameLength
    ents <- assert_total $ traverse genMaybeNodeB entries
    pure $ Just $ DirB name ents

-- public export
-- genFilesystemB : {cfg : NodeParams} -> 
--                  (fs : Filesystem cfg sz) -> 
--                  Gen NonEmpty (FilesystemB fs)
-- genFilesystemB (Root entries) = RootB <$> traverse genMaybeNodeB entries


%language ElabReflection
%runElab deriveIndexed "IsSucc" [Show]
%runElab derive "NodeParams" [Show]
%runElab derive "Metadata" [Show]
%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["Node", "MaybeNode", "HVectMaybeNode"]
%runElab deriveIndexed "Filesystem" [Show]

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
