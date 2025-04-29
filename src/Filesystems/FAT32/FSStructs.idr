module Filesystems.FAT32.FSStructs

import Data.Nat
import Data.Bits
import Deriving.DepTyCheck.Gen
import Data.SnocVect
import Data.Monomorphic.Vect
import Filesystems.FAT32.Utils
import Control.Monad.Pure
import Data.Array.Core
import Data.Array.Mutable

%default total
%hide Data.Array.Index.lsl
%hide Data.Array.Index.refl
%hide Data.Nat.divCeilNZ

ind2 : (0 t : Nat -> Nat -> Type) -> (forall n, m. t n m -> t (S n) (S m)) -> (k : Nat) -> t n m -> t (k+n) (k+m)
ind2 t f 0     x = x
ind2 t f (S k) x = f (ind2 t f k x)

%hint
LTE_Workaround : LTE a b => LTE (100+a) (100+b)
LTE_Workaround @{prf} = ind2 LTE LTESucc 100 prf

public export
genFin : (n : Nat) -> Gen MaybeEmpty (Fin n)
genFin n = do
    (c ** cp) <- elements' $ the (List _) $ boundedRangeDLT 0 n
    pure $ natToFinLT c @{cp}


allFins'' : (k : Nat) -> SnocVect k (Fin k)
allFins'' 0 = [<]
allFins'' 1 = [< FZ]
allFins'' (S $ S k) = let sx := allFins'' (S k) in believe_me sx :< FS (deah sx)

allFins' : (n : Nat) -> Vect n (Fin n)
allFins' n = asVect $ allFins'' n

public export
genMap : (k : Nat) -> (n : Nat) -> (0 _ : IsSucc k) => Gen MaybeEmpty $ Vect k (Fin $ k + n)
genMap k@(S k') n = do
    let xs = allFins' $ k + n
    let ys = weakenN n <$> allFins' k
    rands <- for ys $ \x => choose (x, last)
    let zs = runPure $ do
        ar <- unsafeMArray $ k + n
        lift1 $ writeVect ar xs
        for (zip rands ys) $ \(j, i) => do
            vi <- lift1 $ get ar i
            vj <- lift1 $ get ar j
            lift1 $ set ar j vi
            pure vj
    pure zs

public export
interface ByteRepr a n | n where
    byteRepr : a -> Vect n Bits8

public export
ByteRepr Bits8 1 where
    byteRepr x = [cast x]

public export
ByteRepr Bits16 2 where
    byteRepr n = cast <$> [ n .&. 0xff
                          , n `shiftR` 8
                          ]
public export
ByteRepr Bits32 4 where
    byteRepr n = cast <$> [ n .&. 0xff
                 , (n `shiftR` 8) .&. 0xff
                 , (n `shiftR` 16) .&. 0xff
                 , (n `shiftR` 24) .&. 0xff
                 ]

public export
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


public export
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
    {auto 0 bytsNZ : IsSucc bytsPerSec}
    {auto 0 sectPrf : LTE 512 bytsPerSec}
    {auto 0 rsvPrf : LTE 8 rsvdSecCnt}
    {auto nfatsPrf : LTE 1 numFats}
    {auto 0 sizePrf : n = rsvdSecCnt * bytsPerSec + (numFats * (fatSz * bytsPerSec) + dataClust * clustSize)}
    {auto 0 tclsPrf : m = dataClust}
    {auto 0 csPrf : cs = clustSize}
    {auto 0 fatPrf : fatSz = divCeilNZ (8 + dataClust * 4) bytsPerSec @{bytsNZ}}

export
genBootSectorData : (clustSize : Nat) -> (dataClust : Nat) -> (rootClust : Nat) -> Gen MaybeEmpty (n ** BootSectorData clustSize dataClust n)
genBootSectorData clustSize dataClust rootClust = do
    let bytsPerSec : Nat
        bytsPerSec   = 512
    let secPerClus   = divNatNZ clustSize bytsPerSec %search
    let rsvdSecCnt : Nat 
        rsvdSecCnt   = 32
    let numFats : Nat
        numFats = 2
    let fatSz : Nat        
        fatSz = divCeilNZ (8 + dataClust * 4) bytsPerSec 
    activeFat       <- genFin numFats
    onlyOneFat      <- elements' $ the (List _) [False, True]
    -- let onlyOneFat = False
    mediaType       <- elements' $ the (List _) [0xF0, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF]
    let totalSize : Nat
        totalSize = rsvdSecCnt * bytsPerSec + (numFats * (fatSz * bytsPerSec) + dataClust * clustSize)
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


public export
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

export
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

export
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


public export
record FSInfo where
    constructor MkFSInfo
    fsi_LeadSig    : Vect   4 Bits8 
    fsi_Reserved1  : Vect 480 Bits8
    fsi_StrucSig   : Vect   4 Bits8
    fsi_Free_Count : Vect   4 Bits8
    fsi_Nxt_Free   : Vect   4 Bits8
    fsi_Reserved2  : Vect  12 Bits8
    fsi_TrailSig   : Vect   4 Bits8

export
packFSInfo : FSInfo -> Vect 512 Bits8
packFSInfo x = x.fsi_LeadSig    
            ++ x.fsi_Reserved1 
            ++ x.fsi_StrucSig  
            ++ x.fsi_Free_Count
            ++ x.fsi_Nxt_Free  
            ++ x.fsi_Reserved2 
            ++ x.fsi_TrailSig  

export
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
