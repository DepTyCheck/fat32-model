module Filesystems.FAT32.Pretty


import Filesystems.FAT32
import Filesystems.FAT32.Derived.Node
import Filesystems.FAT32.Derived.NameTree
import Data.UniqFinVect
import Data.UniqFinVect.Derived
import Data.Buffer.Core
import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Control.Monad.Pure
import Data.Bits
import Data.Buffer
import Data.Fin
import Data.Fin.Properties
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Filesystems.FAT32.AuxProofs
import Debug.Trace

%default total
%hide Data.Array.Index.lsl
%hide Data.Array.Index.refl

ind2 : (0 t : Nat -> Nat -> Type) -> (forall n, m. t n m -> t (S n) (S m)) -> (k : Nat) -> t n m -> t (k+n) (k+m)
ind2 t f 0     x = x
ind2 t f (S k) x = f (ind2 t f k x)

%hint
LTE_Workaround : LTE a b => LTE (100+a) (100+b)
LTE_Workaround @{prf} = ind2 LTE LTESucc 100 prf

public export
multLteMonotone : {a, b, c, d : Nat} -> LTE a b -> LTE c d -> LTE (a * c) (b * d)
multLteMonotone x y = multLteMonotoneLeft a b c x `transitive` multLteMonotoneRight b c d y

interface ByteRepr a n | n where
    byteRepr : a -> Vect n Bits8

ByteRepr Bits8 1 where
    byteRepr x = [cast x]

ByteRepr Bits16 2 where
    byteRepr n = cast <$> [ n .&. 0xff
                          , n `shiftR` 8
                          ]

ByteRepr Bits32 4 where
    byteRepr n = cast <$> [ n .&. 0xff
                 , (n `shiftR` 8) .&. 0xff
                 , (n `shiftR` 16) .&. 0xff
                 , (n `shiftR` 24) .&. 0xff
                 ]

ByteRepr Bits64 8 where
    byteRepr n = cast <$> [ n .&. 0xff
                 , (n `shiftR` 8) .&. 0xff
                 , (n `shiftR` 16) .&. 0xff
                 , (n `shiftR` 24) .&. 0xff
                 , (n `shiftR` 32) .&. 0xff
                 , (n `shiftR` 40) .&. 0xff
                 , (n `shiftR` 48) .&. 0xff
                 , (n `shiftR` 56) .&. 0xff
                 ]


record BootSectorData cs m n where
    constructor MkBootSectorData
    clustSize  : Nat
    dataClust  : Nat
    rootClust  : Nat
    bytsPerSec : Nat
    secPerClus : Nat
    rsvdSecCnt : Nat
    numFats    : Nat
    fatSz      : Nat
    activeFat  : Fin numFats
    onlyOneFat : Bool
    mediaType  : Bits8
    {auto 0 sectPrf : LTE 512 bytsPerSec}
    {auto 0 rsvPrf : LTE 8 rsvdSecCnt}
    {auto nfatsPrf : LTE 1 numFats}
    {auto 0 sizePrf : n = rsvdSecCnt * bytsPerSec + (numFats * (8 + dataClust * 4) + dataClust * clustSize)}
    {auto 0 tclsPrf : m = dataClust}
    {auto 0 csPrf : cs = clustSize}

genBootSectorData : (clustSize : Nat) -> (dataClust : Nat) -> (rootClust : Nat) -> Gen MaybeEmpty (n ** BootSectorData clustSize dataClust n)
genBootSectorData clustSize dataClust rootClust = do
    let bytsPerSec : Nat
        bytsPerSec   = 512
    let secPerClus   = divNatNZ clustSize bytsPerSec %search
    let rsvdSecCnt : Nat 
        rsvdSecCnt   = 32
    let numFats : Nat
        numFats = 2
    let fatSz        = divCeilNZ (dataClust * 4) bytsPerSec %search 
    activeFat       <- genFin numFats
    -- onlyOneFat      <- elements' $ the (List _) [False, True]
    let onlyOneFat = False
    mediaType       <- elements' $ the (List _) [0xF0, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF]
    let totalSize : Nat
        totalSize = rsvdSecCnt * bytsPerSec + (numFats * (8 + dataClust * 4) + dataClust * clustSize)
    pure $ (totalSize ** MkBootSectorData { clustSize
                                          , dataClust
                                          , rootClust
                                          , bytsPerSec
                                          , secPerClus
                                          , rsvdSecCnt
                                          , numFats
                                          , fatSz
                                          , activeFat
                                          , onlyOneFat
                                          , mediaType
                                          })


record BootSector where
    constructor MkBootSector
    bs_jmpBoot     : Vect  3 Bits8 
    bs_OEMName     : Vect  8 Bits8
    bpb_BytsPerSec : Vect  2 Bits8
    bpb_SecPerClus : Vect  1 Bits8
    bpb_RsvdSecCnt : Vect  2 Bits8
    bpb_NumFATs    : Vect  1 Bits8
    bpb_RootEntCnt : Vect  2 Bits8
    bpb_TotSec16   : Vect  2 Bits8
    bpb_Media      : Vect  1 Bits8
    bpb_FATSz16    : Vect  2 Bits8
    bpb_SecPerTrk  : Vect  2 Bits8
    bpb_NumHeads   : Vect  2 Bits8
    bpb_HiddSec    : Vect  4 Bits8
    bpb_TotSec32   : Vect  4 Bits8
    bpb_FATSz32    : Vect  4 Bits8
    bpb_ExtFlags   : Vect  2 Bits8
    bpb_FSVer      : Vect  2 Bits8
    bpb_RootClus   : Vect  4 Bits8
    bpb_FSInfo     : Vect  2 Bits8
    bpb_BkBootSec  : Vect  2 Bits8
    bpb_Reserved   : Vect 12 Bits8
    bs_DrvNum      : Vect  1 Bits8
    bs_Reserved1   : Vect  1 Bits8
    bs_BootSig     : Vect  1 Bits8
    bs_VolID       : Vect  4 Bits8
    bs_VolLab      : Vect 11 Bits8
    bs_FilSysType  : Vect  8 Bits8
-- %runElab derive "BootSector" [Barbie]

packBootSect : BootSector -> Vect 512 Bits8
packBootSect x = x.bs_jmpBoot 
              ++ x.bs_OEMName
              ++ x.bpb_BytsPerSec
              ++ x.bpb_SecPerClus
              ++ x.bpb_RsvdSecCnt
              ++ x.bpb_NumFATs
              ++ x.bpb_RootEntCnt
              ++ x.bpb_TotSec16
              ++ x.bpb_Media
              ++ x.bpb_FATSz16
              ++ x.bpb_SecPerTrk
              ++ x.bpb_NumHeads
              ++ x.bpb_HiddSec
              ++ x.bpb_TotSec32
              ++ x.bpb_FATSz32
              ++ x.bpb_ExtFlags
              ++ x.bpb_FSVer
              ++ x.bpb_RootClus
              ++ x.bpb_FSInfo
              ++ x.bpb_BkBootSec
              ++ x.bpb_Reserved
              ++ x.bs_DrvNum
              ++ x.bs_Reserved1
              ++ x.bs_BootSig
              ++ x.bs_VolID
              ++ x.bs_VolLab
              ++ x.bs_FilSysType
              ++ replicate 420 0
              ++ [0x55, 0xAA]

genBootSector : BootSectorData cs m n -> Gen MaybeEmpty BootSector
genBootSector bsdata = do
    bs_jmpBoot         <- oneOf $ alternativesOf (do pure [0xEB, !genBits8, 0x90])
                            ++ alternativesOf (do pure [0xE9, !genBits8, !genBits8])
    bs_OEMName         <- toVect <$> genVectBits8 _
    -- TODO: generate powers of 2 from 512 to clustSize
    let bpb_BytsPerSec  = byteRepr $ cast bsdata.bytsPerSec
    let bpb_SecPerClus  = byteRepr $ cast $ bsdata.secPerClus
    -- TODO: maybe add some sectors for fun here
    let bpb_RsvdSecCnt  = byteRepr $ cast bsdata.rsvdSecCnt
    -- TODO: generate from 1 to 8 FATs
    let bpb_NumFATs     = byteRepr $ cast bsdata.numFats
    let bpb_RootEntCnt  = byteRepr 0
    let bpb_TotSec16    = byteRepr 0
    let bpb_Media       = byteRepr bsdata.mediaType
    let bpb_FATSz16     = byteRepr 0
    bpb_SecPerTrk      <- toVect <$> genVectBits8 _
    bpb_NumHeads       <- toVect <$> genVectBits8 _
    let bpb_HiddSec     = byteRepr 0
    let tFATSz32        = bsdata.fatSz
    let bpb_TotSec32    = byteRepr $ cast $ bsdata.rsvdSecCnt + bsdata.numFats * bsdata.fatSz + bsdata.dataClust * bsdata.secPerClus
    let bpb_FATSz32     = byteRepr $ cast bsdata.fatSz
    -- TODO: generate mirroring and stuff
    let bpb_ExtFlags    = byteRepr $ cast (finToNat bsdata.activeFat) .|. (the Bits16 (if bsdata.onlyOneFat then 1 else 0) `shiftL` 7)
    let bpb_FSVer       = byteRepr 0
    let bpb_RootClus    = byteRepr $ cast bsdata.rootClust
    let bpb_FSInfo      = byteRepr 1
    let bpb_BkBootSec   = byteRepr 6
    let bpb_Reserved    = replicate _ 0
    let bs_DrvNum       = byteRepr 0x80
    let bs_Reserved1    = replicate _ 0
    let bs_BootSig      = byteRepr 0x29
    bs_VolID           <- toVect <$> genVectBits8 _
    let bs_VolLab       = map cast ['N', 'O', ' ', 'N', 'A', 'M', 'E', ' ', ' ', ' ', ' ']
    -- bs_VolLab          <- packVect <$> genVectBits8 _
    let bs_FilSysType   = map cast ['F', 'A', 'T', '3', '2', ' ', ' ', ' ']
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
    fsi_LeadSig    : Vect   4 Bits8 
    fsi_Reserved1  : Vect 480 Bits8
    fsi_StrucSig   : Vect   4 Bits8
    fsi_Free_Count : Vect   4 Bits8
    fsi_Nxt_Free   : Vect   4 Bits8
    fsi_Reserved2  : Vect  12 Bits8
    fsi_TrailSig   : Vect   4 Bits8

packFSInfo : FSInfo -> Vect 512 Bits8
packFSInfo x = x.fsi_LeadSig    
            ++ x.fsi_Reserved1 
            ++ x.fsi_StrucSig  
            ++ x.fsi_Free_Count
            ++ x.fsi_Nxt_Free  
            ++ x.fsi_Reserved2 
            ++ x.fsi_TrailSig  


genFsInfo : (dataClust : Nat) -> Gen MaybeEmpty FSInfo
genFsInfo dataClust = do
  let fsi_LeadSig   = byteRepr 0x41615252
  let fsi_Reserved1 = replicate _ 0
  let fsi_StrucSig  = byteRepr 0x61417272
  fsi_Free_Count   <- map (byteRepr . cast) $ choose (0, dataClust)
  fsi_Nxt_Free     <- map (byteRepr . cast) $ choose (0, (minus dataClust 1))
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

padBlob : (clustSize : Nat) -> (0 clustNZ : IsSucc clustSize) -> {n : Nat} -> SnocVectBits8 n -> SnocVectBits8 (divCeilNZ n clustSize @{clustNZ} * clustSize)
padBlob clustSize clustNZ sx with (DivisionTheorem n clustSize clustNZ clustNZ, boundModNatNZ n clustSize clustNZ) | (modNatNZ n clustSize clustNZ)
    _ | (cc, blt) | 0  = rewrite sym cc in sx
    _ | (cc, blt) | m@(S k) = do
      rewrite sym $ cong (+ divNatNZ n clustSize clustNZ * clustSize) $ plusMinusLte m clustSize (lteSuccLeft blt)
      rewrite sym $ plusAssociative (minus clustSize m) m (divNatNZ n clustSize clustNZ * clustSize)
      rewrite sym cc
      rewrite plusCommutative (minus clustSize m) n
      sx <>< (replicate (minus clustSize m) 0)


serializeMeta : Metadata -> Bits8
serializeMeta (MkMetadata readOnly hidden system archive) = 
    0 .|. (if readOnly then 0x1 else 0)
      .|. (if hidden then 0x2 else 0)
      .|. (if system then 0x4 else 0)
      .|. (if archive then 0x20 else 0)

repr32' : Bits32 -> VectBits8 4
repr32' m = [ cast $ m .&. 0xff
            , cast $ (m `shiftR` 8) .&. 0xff
            , cast $ (m `shiftR` 16) .&. 0xff
            , cast $ (m `shiftR` 24) .&. 0xff
            ]

repr32'' : Bits32 -> IBuffer 4 
repr32'' m = buffer [ cast $ m .&. 0xff
                    , cast $ (m `shiftR` 8) .&. 0xff
                    , cast $ (m `shiftR` 16) .&. 0xff
                    , cast $ (m `shiftR` 24) .&. 0xff
                    ]

emptyDirent : VectBits8 DirentSize
emptyDirent = 0xE5 :: replicate _ 0

dotDirent : VectBits8 DirentSize
dotDirent = cast '.' :: replicate 10 (cast ' ') ++ replicate _ 0

dotdotDirent : VectBits8 DirentSize
dotdotDirent = cast '.' :: cast '.' :: replicate 9 (cast ' ') ++ replicate _ 0

-- TODO: date and time generation
-- TODO: proper volume labels
makeDirent : {clustSize : Nat} -> (0 clustNZ : IsSucc clustSize) => MaybeNode (MkNodeCfg clustSize) (MkNodeArgs cur tot @{ctprf}) True False -> Filename -> (clustNum : Nat) -> VectBits8 DirentSize
makeDirent node fname cnum with (repr32' $ cast cnum)
    makeDirent (Just $ FileB meta x {k=0}) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ serializeMeta meta :: replicate _ 0
    makeDirent (Just $ FileB meta x {k=S k'}) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ serializeMeta meta :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ repr32' (cast $ S k')
    makeDirent (Just $ Dir meta entries) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ (serializeMeta meta .|. 0x10) :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ replicate 4 0
    makeDirent Nothing _ _ | _ = emptyDirent

-- TODO: some free clusters can also be marked bad
-- TODO: first 4 bits can actually be randomised
mapRangeWithNextVal : List (Subset Nat (`LT` b)) -> List (Subset Nat (`LT` b), Nat) 
mapRangeWithNextVal [] = []
mapRangeWithNextVal (x :: []) = [(x, 0x0FFFFFF8)]
mapRangeWithNextVal (x :: (y@(Element fst snd) :: xs)) = (x, 2 + fst) :: mapRangeWithNextVal (y::xs)

writeBlob : (clustSize' : Nat) ->
            (0 clustNZ : IsSucc clustSize') =>
            {k : Nat} ->
            (blob : SnocVectBits8 k) ->
            (currClust : Nat) ->
            (cmap : IArray cls (Fin tcls)) ->
            (dataOffset : Nat) ->
            (fatOffset : Nat) ->
            (0 clsBounds : LTE (currClust + divCeilNZ k clustSize') cls) =>
            (0 tszBounds : LTE (dataOffset + tcls * clustSize') tsz) =>
            (0 fatBounds : LTE (fatOffset + tcls * 4) tsz) =>
            (image : MBuffer s tsz) ->
            Pure s ()
writeBlob clustSize' blob currClust cmap dataOffset fatOffset image = do
    let blobBuf = packVect $ padBlob clustSize' clustNZ blob
    for_ (mapRangeWithNextVal $ boundedRangeLT 0 (divCeilNZ k clustSize')) $ forFile blobBuf
    where forFile : IBuffer (divCeilNZ k clustSize' * clustSize') -> (Subset Nat (`LT` divCeilNZ k clustSize'), Nat) -> Pure s ()
          forFile bbuf (Element cl clp, nxt) = do
              let absclust : Fin tcls
                  absclust = atNat cmap (currClust + cl) @{
                      rewrite plusSuccRightSucc currClust cl
                      in plusLteMonotoneLeft currClust (S cl) (divCeilNZ k clustSize') clp
                              `transitive` clsBounds
                  }
              lift1 $ icopy bbuf (cl * clustSize') (dataOffset + finToNat absclust * clustSize') clustSize' image @{ do
                  rewrite plusCommutative (cl * clustSize') clustSize'
                  (multLteMonotoneLeft (S cl) (divCeilNZ k clustSize') clustSize' clp)
              } @{ do
                  rewrite sym $ plusAssociative dataOffset (finToNat absclust * clustSize') clustSize'
                  rewrite plusCommutative (finToNat absclust * clustSize') clustSize'
                  (plusLteMonotoneLeft dataOffset _ _ $ multLteMonotoneLeft _ tcls clustSize' $ elemSmallerThanBound absclust) `transitive` tszBounds
              }
              let val = repr32'' $ cast nxt
              lift1 $ icopy val 0 (fatOffset + finToNat absclust * 4) 4 image @{Relation.reflexive} @{do
                  rewrite sym $ plusAssociative fatOffset (finToNat absclust * 4) 4
                  rewrite plusCommutative (finToNat absclust * 4) 4
                  plusLteMonotoneLeft fatOffset _ _ (multLteMonotoneLeft _ _ 4 $ elemSmallerThanBound absclust) `transitive` fatBounds
              }



mapNodesAndNamesToDirents : {clustSize : Nat} ->
           (0 clustNZ : IsSucc clustSize) =>
           (nodes : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars True False) ->
           (names : UniqNames nodes) ->
           (currClust : Nat) ->
           SnocVectBits8 (DirentSize * k)
mapNodesAndNamesToDirents [<] Empty _ = [<]
mapNodesAndNamesToDirents ((:<) sx x {ar=MkNodeArgs cur tot} {k=k'}) (NewName @{ff} f) currClust =
    replace {p = SnocVectBits8} (plusCommutative (DirentSize * k') DirentSize `trans` (sym $ multRightSuccPlus DirentSize k')) $ mapNodesAndNamesToDirents sx ff (currClust + tot) <>< makeDirent x f currClust

public export
serializeNode : {clustSize' : Nat} ->
                (0 clustNZ : IsSucc clustSize') =>
                {cur : Nat} ->
                {tot : Nat} ->
                {0 ctprf : LTE cur tot} ->
                (node : Node (MkNodeCfg clustSize') (MkNodeArgs cur tot @{ctprf}) True fs) ->
                (currClust : Nat) ->
                (names : NameTree node) ->
                (cmap : IArray cls (Fin tcls)) ->
                (dataOffset : Nat) ->
                (fatOffset : Nat) ->
                (0 clsBounds : LTE (currClust + tot) cls) =>
                (0 tszBounds : LTE (dataOffset + tcls * clustSize') tsz) =>
                (0 fatBounds : LTE (fatOffset + tcls * 4) tsz) =>
                (image : MBuffer s tsz) ->
                Pure s ()

forNodesAndNameTrees_ : {clustSize' : Nat} ->
                        (0 clustNZ : IsSucc clustSize') =>
                        (nodes : HSnocVectMaybeNode (MkNodeCfg clustSize') k ars True False) ->
                        (nameTrees : HSnocVectNameTree nodes) ->
                        (currClust : Nat) ->
                        (cmap : IArray cls (Fin tcls)) ->
                        (dataOffset : Nat) ->
                        (fatOffset : Nat) ->
                        (0 clsBounds : LTE (currClust + totsum ars) cls) =>
                        (0 tszBounds : LTE (dataOffset + tcls * clustSize') tsz) =>
                        (0 fatBounds : LTE (fatOffset + tcls * 4) tsz) =>
                        (image : MBuffer s tsz) ->
                        Pure s ()
forNodesAndNameTrees_ [<] [<] currClust cmap dataOffset fatOffset image = pure ()
forNodesAndNameTrees_ ((:<) sx (Just x) {ar=MkNodeArgs cur tot @{ctprf}} {ars=ars'}) (sy :< (Just y)) currClust cmap dataOffset fatOffset image = do
    serializeNode x currClust y cmap dataOffset fatOffset image @{%search} @{plusLteMonotoneLeft currClust _ _ (totsumLTE {cur} {ctprf}) `transitive` clsBounds}
    forNodesAndNameTrees_ sx sy (currClust + tot) cmap dataOffset fatOffset image @{%search} @{rewrite sym $ plusAssociative currClust tot (totsum ars') in clsBounds}
forNodesAndNameTrees_ ((:<) sx Nothing {ar=MkNodeArgs cur tot @{ctprf}} {ars=ars'}) (sy :< Nothing) currClust cmap dataOffset fatOffset image = forNodesAndNameTrees_ sx sy (currClust + tot) cmap dataOffset fatOffset image @{%search} @{rewrite sym $ plusAssociative currClust tot (totsum ars') in clsBounds}


serializeNode (FileB meta blob {k}) currClust names cmap dataOffset fatOffset image = 
    writeBlob clustSize' blob currClust cmap dataOffset fatOffset image
serializeNode (Dir meta nodes {k} {ars}) currClust (Dir names nameTrees {nodes}) cmap dataOffset fatOffset image = do
    writeBlob clustSize' (replace {p = SnocVectBits8} (sym $ multDistributesOverPlusRight DirentSize 2 k) $ ([<] <>< dotDirent <>< dotdotDirent) ++ mapNodesAndNamesToDirents nodes names (currClust + cur)) currClust cmap dataOffset fatOffset image {k = DirentSize * (2 + k)} @{%search} @{plusLteMonotoneLeft currClust _ _ ctprf `transitive` clsBounds}
    forNodesAndNameTrees_ nodes nameTrees (currClust + cur) cmap dataOffset fatOffset image @{%search} @{rewrite sym $  plusAssociative currClust cur (totsum ars) in clsBounds}
serializeNode (Root nodes {k} {ars}) currClust (Root names nameTrees {nodes}) cmap dataOffset fatOffset image = do
    writeBlob clustSize' (mapNodesAndNamesToDirents nodes names (currClust + cur)) currClust cmap dataOffset fatOffset image @{%search} @{plusLteMonotoneLeft currClust _ _ ctprf `transitive` clsBounds}
    forNodesAndNameTrees_ nodes nameTrees (currClust + cur) cmap dataOffset fatOffset image @{%search} @{rewrite sym $  plusAssociative currClust cur (totsum ars) in clsBounds}
serializeNode _ _ _ _ _ _ _ = pure ()

-- Layout:
-- 32 reserved sectors, which includes:
-- sector 0: boot sector
-- sector 1: fsinfo
-- sector 6: boot sector copy
-- sector 7: fsinfo copy
-- FAT tables
-- data area
--
-- Generation:
-- copy bootsector (twice) (make sure to fill offsets 510 and 511)
-- copy fsinfo (twice) (make sure to fill offsets 510 and 511?)
-- copy FAT to active slot (0 if mirroring enabled)
-- fill FAT[0] and FAT[1]
-- copy FAT to other slots if mirroring enabled
-- (TODO: fill inactive FATs with garbage)
-- copy data area

eqToLTE : {b : Nat} -> a = b -> LTE a b
eqToLTE Refl = reflexive


buildImage : {clustSize' : Nat} ->
             (0 clustNZ : IsSucc clustSize') =>
             (bdata : BootSectorData clustSize' tcls tsz) ->
             (bsect : BootSector) ->
             (fsinfo : FSInfo) ->
             {cur : Nat} ->
             {tot : Nat} ->
             {0 ctprf : LTE cur tot} ->
             (node : Node (MkNodeCfg clustSize') (MkNodeArgs cur tot @{ctprf}) True True) ->
             (names : NameTree node) ->
             (cmap : IArray tot (Fin tcls)) ->
             (image : MBuffer s tsz) ->
             Pure s ()
buildImage bdata bsect fsinfo node names cmap image = do
    let pBsect = buffer $ packBootSect bsect
    let pFsinfo = buffer $ packFSInfo fsinfo
    let fat0 = repr32'' $ 0x0FFFFF00 .|. cast bdata.mediaType
    let fat1 = repr32'' 0x0FFFFFF8
    
    lift1 $ icopy pBsect 0 0 512 image @{reflexive} @{rewrite bdata.sizePrf in (%search `transitive` multLteMonotone bdata.rsvPrf bdata.sectPrf) `transitive` lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec)}
    
    lift1 $ icopy pBsect 0 (6 * bdata.bytsPerSec) 512 image @{reflexive} @{rewrite bdata.sizePrf in ((plusLteMonotoneRight 512 _ _ (multLteMonotoneLeft 6 7 bdata.bytsPerSec %search) `transitive` plusLteMonotoneLeft (7 * bdata.bytsPerSec) 512 bdata.bytsPerSec bdata.sectPrf) `transitive` (eqToLTE (plusCommutative (7 * bdata.bytsPerSec) bdata.bytsPerSec) `transitive` multLteMonotoneLeft 8 bdata.rsvdSecCnt bdata.bytsPerSec bdata.rsvPrf)) `transitive` lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec)}
    
    lift1 $ icopy pFsinfo 0 (1 * bdata.bytsPerSec) 512 image @{reflexive} @{rewrite bdata.sizePrf in ((plusLteMonotoneRight 512 _ _ (multLteMonotoneLeft 1 7 bdata.bytsPerSec %search) `transitive` plusLteMonotoneLeft (7 * bdata.bytsPerSec) 512 bdata.bytsPerSec bdata.sectPrf) `transitive` (eqToLTE (plusCommutative (7 * bdata.bytsPerSec) bdata.bytsPerSec) `transitive` multLteMonotoneLeft 8 bdata.rsvdSecCnt bdata.bytsPerSec bdata.rsvPrf)) `transitive` lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec)}
    
    lift1 $ icopy pFsinfo 0 (7 * bdata.bytsPerSec) 512 image @{reflexive} @{rewrite bdata.sizePrf in ((plusLteMonotoneRight 512 _ _ (multLteMonotoneLeft 7 7 bdata.bytsPerSec reflexive) `transitive` plusLteMonotoneLeft (7 * bdata.bytsPerSec) 512 bdata.bytsPerSec bdata.sectPrf) `transitive` (eqToLTE (plusCommutative (7 * bdata.bytsPerSec) bdata.bytsPerSec) `transitive` multLteMonotoneLeft 8 bdata.rsvdSecCnt bdata.bytsPerSec bdata.rsvPrf)) `transitive` lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec)}
    
    when bdata.onlyOneFat $ do
        serializeNode node 0 names cmap (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)) (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4) + 8) image @{%search} @{reflexive} @{ do
            rewrite bdata.csPrf
            replace {p = \x => LTE x tsz} ((bdata.sizePrf `trans` plusAssociative _ _ _) `trans` cong (\x => (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + x * bdata.clustSize)) (sym bdata.tclsPrf)) reflexive
        } @{ CalcSmart $
            |~ bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4) + 8 + (tcls * 4)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4) + 8 + (bdata.dataClust * 4)
                ... cong (\x => bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4) + 8 + (x * 4)) bdata.tclsPrf
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)
                ... eqPrf1 (bdata.rsvdSecCnt * bdata.bytsPerSec) (finToNat bdata.activeFat) 8 (bdata.dataClust * 4)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S $ finToNat bdata.activeFat) bdata.numFats (8 + bdata.dataClust * 4) (elemSmallerThanBound bdata.activeFat))
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        }
        lift1 $ icopy fat0 0 (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)) 4 @{%search} @{ CalcSmart $
            |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)) + 4
            <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)) + (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)) 4 (8 + bdata.dataClust * 4) (lteAddRight 4)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)
                ... eqPrf3 (bdata.rsvdSecCnt * bdata.bytsPerSec) (finToNat bdata.activeFat) 8 (bdata.dataClust * 4)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S $ finToNat bdata.activeFat) bdata.numFats (8 + bdata.dataClust * 4) (elemSmallerThanBound bdata.activeFat))
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        } image
        lift1 $ icopy fat1 0 ((bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)) + 4) 4 @{%search} @{ CalcSmart $
            |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (8 + bdata.dataClust * 4))) + 4 + 4
            ~~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (8 + bdata.dataClust * 4))) + 8
                ..< plusAssociative _ _ _
            <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (8 + bdata.dataClust * 4))) + (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft ((bdata.rsvdSecCnt * bdata.bytsPerSec) + (finToNat (bdata.activeFat) * (8 + bdata.dataClust * 4))) 8 (8 + bdata.dataClust * 4) (lteAddRight 8)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + finToNat bdata.activeFat) * (8 + bdata.dataClust * 4)
                ... eqPrf3 (bdata.rsvdSecCnt * bdata.bytsPerSec) (finToNat bdata.activeFat) 8 (bdata.dataClust * 4)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S $ finToNat bdata.activeFat) bdata.numFats (8 + bdata.dataClust * 4) (elemSmallerThanBound bdata.activeFat))
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        } image
    when (not bdata.onlyOneFat) $ do
        serializeNode node 0 names cmap (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)) (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4) + 8) image @{%search} @{reflexive} @{ do
            rewrite bdata.csPrf
            replace {p = \x => LTE x tsz} ((bdata.sizePrf `trans` plusAssociative _ _ _) `trans` cong (\x => (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + x * bdata.clustSize)) (sym bdata.tclsPrf)) reflexive
        } @{ CalcSmart $
            |~ bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4) + 8 + (tcls * 4)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4) + 8 + (bdata.dataClust * 4)
                ... cong (\x => bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4) + 8 + (x * 4)) bdata.tclsPrf
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (8 + bdata.dataClust * 4)
                ... eqPrf1 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 8 (bdata.dataClust * 4)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (8 + bdata.dataClust * 4) bdata.nfatsPrf)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        }
        lift1 $ icopy fat0 0 (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4)) 4 @{%search} @{ CalcSmart $
            |~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (8 + bdata.dataClust * 4)) + 4
            <~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (8 + bdata.dataClust * 4)) + (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (8 + bdata.dataClust * 4)) 4 (8 + bdata.dataClust * 4) (lteAddRight 4)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (8 + bdata.dataClust * 4)
                ... eqPrf3 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 8 (bdata.dataClust * 4)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (8 + bdata.dataClust * 4) bdata.nfatsPrf)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        } image
        lift1 $ icopy fat1 0 ((bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4)) + 4) 4 @{%search} @{ CalcSmart $
            |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4)) + 4 + 4
            ~~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4)) + 8
                ..< plusAssociative _ _ _
            <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4)) + (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (8 + bdata.dataClust * 4)) 8 (8 + bdata.dataClust * 4) (lteAddRight 8)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (8 + bdata.dataClust * 4)
                ... eqPrf3 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 8 (bdata.dataClust * 4)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (8 + bdata.dataClust * 4) bdata.nfatsPrf)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        } image
        for_ (boundedRangeLT 1 bdata.numFats @{bdata.nfatsPrf}) $ \(Element f fp) => do
            lift1 $ copy image
                (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (8 + bdata.dataClust * 4))
                (bdata.rsvdSecCnt * bdata.bytsPerSec + f * (8 + bdata.dataClust * 4))
                (8 + bdata.dataClust * 4) image 
                @{ CalcSmart $
                    |~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (8 + bdata.dataClust * 4)) + (8 + bdata.dataClust * 4)
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (8 + bdata.dataClust * 4)
                        ... eqPrf3 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 8 (bdata.dataClust * 4)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                        ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (8 + bdata.dataClust * 4) bdata.nfatsPrf)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                        ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                        ..< plusAssociative _ _ _ 
                    ~~ tsz
                        ..< bdata.sizePrf
                }
                @{ CalcSmart $
                    |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (f * (8 + bdata.dataClust * 4))) + (8 + bdata.dataClust * 4)
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + f) * (8 + bdata.dataClust * 4)
                        ... eqPrf3 (bdata.rsvdSecCnt * bdata.bytsPerSec) f 8 (bdata.dataClust * 4)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4)
                        ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S f) bdata.numFats (8 + bdata.dataClust * 4) fp)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize
                        ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (8 + bdata.dataClust * 4))
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (8 + bdata.dataClust * 4) + bdata.dataClust * bdata.clustSize)
                        ..< plusAssociative _ _ _ 
                    ~~ tsz
                        ..< bdata.sizePrf
                }


public export
genImage : (fuel1 : Fuel) -> (fuel2 : Fuel) -> (fuel3 : Fuel) -> (cfg : NodeCfg) -> (minClust : Nat) -> Gen MaybeEmpty (Buffer, Int)
genImage fuel1 fuel2 fuel3 (MkNodeCfg clustSize @{clustNZ}) minClust = do
    (ar@(MkNodeArgs _ tot) ** node) <- trace "generating NodeB..." $ genFilesystemB fuel1 $ MkNodeCfg clustSize
    names <- trace "generating NameTree..." $ genNameTree fuel2 (MkNodeCfg clustSize) ar True True node @{const genBits8} @{const genFilename}
    let tcls : Nat
        tcls = maximum 65525 $ maximum minClust tot
    let tclsPrf = maximumRightUpperBound minClust tot `transitive` maximumRightUpperBound 65525 (maximum minClust tot)
    let genvect = 
            case isItSucc tot of
                (Yes prf) => trace "generating cmap..." $ replace {p = \t => Gen MaybeEmpty (Vect tot (Fin t))} (plusCommutative tot (tcls `minus` tot) `trans` plusMinusLte tot tcls tclsPrf) $ genMap tot (tcls `minus` tot)
                (No contra)    => case tot of
                                       0 => pure []
                                       (S k) => void $ contra ItIsSucc
    cvect <- genvect
    let cmap = array cvect
    let root = 
        case isLT 0 tot of
          (Yes prf) => 2 + finToNat (atNat cmap 0 @{prf})
          (No _)    => 2
    (tsz ** bdata) <- trace "generating bdata..." $ genBootSectorData clustSize tcls root
    bsect <- trace "generating bsect..." $ genBootSector bdata
    fsinfo <- trace "generating fsinfo..." $ genFsInfo tcls
    pure $ runPure $ do
        image <- mbuffer tsz
        trace "building image..." $ buildImage bdata bsect fsinfo node names cmap image
        pure $ (unsafeFromMBuffer image, cast tsz)

