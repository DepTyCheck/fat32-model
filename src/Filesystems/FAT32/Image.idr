module Filesystems.FAT32.Image


import Filesystems.FAT32
import Filesystems.FAT32.NameTree
import Filesystems.FAT32.Derived.Node
import Filesystems.FAT32.Derived.NameTree
import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Control.Monad.Pure
import Data.Bits
import Data.Buffer
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.Fin
import Data.Fin.Properties
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Filesystems.FAT32.Utils
import Filesystems.FAT32.FSStructs
import System.Random.Pure.StdGen
import System

%default total
%prefix_record_projections off
%hide Data.Array.Index.lsl
%hide Data.Array.Index.refl

ind2 : (0 t : Nat -> Nat -> Type) -> (forall n, m. t n m -> t (S n) (S m)) -> (k : Nat) -> t n m -> t (k+n) (k+m)
ind2 t f 0     x = x
ind2 t f (S k) x = f (ind2 t f k x)

%hint
LTE_Workaround : LTE a b => LTE (100+a) (100+b)
LTE_Workaround @{prf} = ind2 LTE LTESucc 100 prf

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

dotDirent : Nat -> VectBits8 DirentSize
dotDirent cnum with (repr32' $ cast cnum)
    dotDirent cnum | (b0::b1::b2::b3::[]) = cast '.' :: replicate 10 (cast ' ') ++ [0x10] ++ replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ replicate 4 0

dotdotDirent : Nat -> VectBits8 DirentSize
dotdotDirent cnum with (repr32' $ cast cnum)
    dotdotDirent cnum | (b0::b1::b2::b3::[]) = cast '.' :: cast '.' :: replicate 9 (cast ' ') ++ [0x10] ++ replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ replicate 4 0

-- TODO: date and time generation
-- TODO: proper volume labels
makeDirent : {clustSize : Nat} -> (0 clustNZ : IsSucc clustSize) => MaybeNode (MkNodeCfg clustSize) (MkNodeArgs cur tot @{ctprf}) Blobful Rootless -> Filename -> (clustNum : Nat) -> VectBits8 DirentSize
makeDirent node fname cnum with (repr32' $ cast cnum)
    makeDirent (Just $ File meta (BlobSome x) {k=0}) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ serializeMeta meta :: replicate _ 0
    makeDirent (Just $ File meta (BlobSome x) {k=S k'}) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ serializeMeta meta :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ repr32' (cast $ S k')
    makeDirent (Just $ Dir meta entries) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ (serializeMeta meta .|. 0x10) :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ replicate 4 0
    makeDirent Nothing _ _ | _ = emptyDirent

-- TODO: some free clusters can also be marked bad
-- TODO: first 4 bits can actually be randomised
mapRangeWithNextVal : List (Subset Nat (`LT` b)) -> List (Subset Nat (`LT` b), Maybe $ Subset Nat (`LT` b)) 
mapRangeWithNextVal [] = []
mapRangeWithNextVal (x :: []) = [(x, Nothing)]
mapRangeWithNextVal (x :: (y :: xs)) = (x, Just y) :: mapRangeWithNextVal (y::xs)

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
    where forFile : IBuffer (divCeilNZ k clustSize' * clustSize') -> (Subset Nat (`LT` divCeilNZ k clustSize'), Maybe $ Subset Nat (`LT` divCeilNZ k clustSize')) -> Pure s ()
          forFile bbuf (Element cl clp, nxt) = do
              let absclust : Fin tcls
                  absclust = atNat cmap (currClust + cl) @{
                      rewrite plusSuccRightSucc currClust cl
                      in plusLteMonotoneLeft currClust (S cl) (divCeilNZ k clustSize') clp
                              `transitive` clsBounds
                  }
              let nxtclust : Nat
                  nxtclust = case nxt of
                                  Nothing => 0x0FFFFFF8
                                  (Just $ Element nx nxp) => 2 + (finToNat $ atNat cmap (currClust + nx) @{
                                      rewrite plusSuccRightSucc currClust nx
                                      in plusLteMonotoneLeft currClust (S nx) (divCeilNZ k clustSize') nxp
                                      `transitive` clsBounds
                                  })
              lift1 $ icopy bbuf (cl * clustSize') (dataOffset + finToNat absclust * clustSize') clustSize' image @{ do
                  rewrite plusCommutative (cl * clustSize') clustSize'
                  (multLteMonotoneLeft (S cl) (divCeilNZ k clustSize') clustSize' clp)
              } @{ do
                  rewrite sym $ plusAssociative dataOffset (finToNat absclust * clustSize') clustSize'
                  rewrite plusCommutative (finToNat absclust * clustSize') clustSize'
                  (plusLteMonotoneLeft dataOffset _ _ $ multLteMonotoneLeft _ tcls clustSize' $ elemSmallerThanBound absclust) `transitive` tszBounds
              }
              let val = repr32'' $ cast nxtclust
              lift1 $ icopy val 0 (fatOffset + finToNat absclust * 4) 4 image @{Relation.reflexive} @{do
                  rewrite sym $ plusAssociative fatOffset (finToNat absclust * 4) 4
                  rewrite plusCommutative (finToNat absclust * 4) 4
                  plusLteMonotoneLeft fatOffset _ _ (multLteMonotoneLeft _ _ 4 $ elemSmallerThanBound absclust) `transitive` fatBounds
              }



mapNodesAndNamesToDirents : {clustSize : Nat} ->
           (0 clustNZ : IsSucc clustSize) =>
           (nodes : HSnocVectMaybeNode (MkNodeCfg clustSize) k ars Blobful) ->
           (names : UniqNames k) ->
           (cmap : IArray cls (Fin tcls)) ->
           (currClust : Nat) ->
           (0 clsBounds : LTE (currClust + totsum ars) cls) =>
           SnocVectBits8 (DirentSize * k)
mapNodesAndNamesToDirents [<] Empty _ _ = [<]
mapNodesAndNamesToDirents ((:<) sx x {ar=MkNodeArgs cur 0} {k=k'}) (NewName @{ff} f) cmap currClust =
    replace {p = SnocVectBits8} (plusCommutative (DirentSize * k') DirentSize `trans` (sym $ multRightSuccPlus DirentSize k')) $ mapNodesAndNamesToDirents sx ff cmap currClust <>< makeDirent x f 0
mapNodesAndNamesToDirents ((:<) sx x {ar=MkNodeArgs cur tot@(S tot')} {k=k'} {ars=ars'}) (NewName @{ff} f) cmap currClust =
    replace {p = SnocVectBits8} (plusCommutative (DirentSize * k') DirentSize `trans` (sym $ multRightSuccPlus DirentSize k')) $ mapNodesAndNamesToDirents sx ff cmap (currClust + tot) @{%search} @{rewrite sym $ plusAssociative currClust tot (totsum ars') in clsBounds} <>< makeDirent x f (2 + (finToNat $ atNat cmap currClust @{(rewrite sym $ plusSuccRightSucc currClust (tot' + totsum ars') in lteAddRight (S currClust) {m = tot' + totsum ars'}) `transitive` clsBounds}))

public export
serializeNode : {clustSize' : Nat} ->
                (0 clustNZ : IsSucc clustSize') =>
                {cur : Nat} ->
                {tot : Nat} ->
                {0 ctprf : LTE cur tot} ->
                (node : Node (MkNodeCfg clustSize') (MkNodeArgs cur tot @{ctprf}) Blobful fs) ->
                (currClust : Nat) ->
                (parentPhys : Nat) ->
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
                        (nodes : HSnocVectMaybeNode (MkNodeCfg clustSize') k ars Blobful) ->
                        (nameTrees : HSnocVectNameTree nodes) ->
                        (currClust : Nat) ->
                        (parentPhys : Nat) ->
                        (cmap : IArray cls (Fin tcls)) ->
                        (dataOffset : Nat) ->
                        (fatOffset : Nat) ->
                        (0 clsBounds : LTE (currClust + totsum ars) cls) =>
                        (0 tszBounds : LTE (dataOffset + tcls * clustSize') tsz) =>
                        (0 fatBounds : LTE (fatOffset + tcls * 4) tsz) =>
                        (image : MBuffer s tsz) ->
                        Pure s ()
forNodesAndNameTrees_ [<] [<] currClust parentPhys cmap dataOffset fatOffset image = pure ()
forNodesAndNameTrees_ ((:<) sx (Just x) {ar=MkNodeArgs cur tot @{ctprf}} {ars=ars'}) (sy :< (Just y)) currClust parentPhys cmap dataOffset fatOffset image = do
    serializeNode x currClust parentPhys y cmap dataOffset fatOffset image @{%search} @{plusLteMonotoneLeft currClust _ _ (totsumLTE {cur} {ctprf}) `transitive` clsBounds}
    forNodesAndNameTrees_ sx sy (currClust + tot) parentPhys cmap dataOffset fatOffset image @{%search} @{rewrite sym $ plusAssociative currClust tot (totsum ars') in clsBounds}
forNodesAndNameTrees_ ((:<) sx Nothing {ar=MkNodeArgs cur tot @{ctprf}} {ars=ars'}) (sy :< Nothing) currClust parentPhys cmap dataOffset fatOffset image = forNodesAndNameTrees_ sx sy (currClust + tot) parentPhys cmap dataOffset fatOffset image @{%search} @{rewrite sym $ plusAssociative currClust tot (totsum ars') in clsBounds}


serializeNode (File meta (BlobSome blob) {k}) currClust _ names cmap dataOffset fatOffset image = 
    writeBlob clustSize' blob currClust cmap dataOffset fatOffset image
serializeNode (Dir meta nodes {k} {ars}) currClust parentPhys (Dir names nameTrees {nodes}) cmap dataOffset fatOffset image = do
    let currPhys : Nat
        currPhys = 2 + (finToNat $ atNat cmap currClust @{(rewrite plusOneRight currClust in plusLteMonotoneLeft currClust _ _ (divCeilIsSucc (DirentSize * (2 + k)) clustSize' `transitive` lteAddRight _ {m = totsum ars})) `transitive` clsBounds})
    writeBlob clustSize' (replace {p = SnocVectBits8} (sym $ multDistributesOverPlusRight DirentSize 2 k) $ ([<] <>< dotDirent currPhys <>< dotdotDirent parentPhys) ++ mapNodesAndNamesToDirents nodes names cmap (currClust + cur) @{%search} @{rewrite sym $ plusAssociative currClust cur (totsum ars) in clsBounds}) currClust cmap dataOffset fatOffset image {k = DirentSize * (2 + k)} @{%search} @{plusLteMonotoneLeft currClust _ _ ctprf `transitive` clsBounds}
    forNodesAndNameTrees_ nodes nameTrees (currClust + cur) currPhys cmap dataOffset fatOffset image @{%search} @{rewrite sym $ plusAssociative currClust cur (totsum ars) in clsBounds}
serializeNode (Root nodes {k} {ars}) currClust _ (Root names nameTrees {nodes}) cmap dataOffset fatOffset image = do
    writeBlob clustSize' (mapNodesAndNamesToDirents nodes names cmap (currClust + cur) @{%search} @{rewrite sym $ plusAssociative currClust cur (totsum ars) in clsBounds}) currClust cmap dataOffset fatOffset image @{%search} @{plusLteMonotoneLeft currClust _ _ ctprf `transitive` clsBounds}
    forNodesAndNameTrees_ nodes nameTrees (currClust + cur) 0 cmap dataOffset fatOffset image @{%search} @{rewrite sym $ plusAssociative currClust cur (totsum ars) in clsBounds}
serializeNode _ _ _ _ _ _ _ _ = pure ()

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


bdataFatPrf : (bdata : BootSectorData cs m n) -> (LTE (8 + bdata.dataClust * 4) (bdata.fatSz * bdata.bytsPerSec))
bdataFatPrf bdata = rewrite bdata.fatPrf in divCeilMultLTE (8 + bdata.dataClust * 4) bdata.bytsPerSec

buildImage : {clustSize' : Nat} ->
             (0 clustNZ : IsSucc clustSize') =>
             (bdata : BootSectorData clustSize' tcls tsz) ->
             (bsect : BootSector) ->
             (fsinfo : FSInfo) ->
             {cur : Nat} ->
             {tot : Nat} ->
             {0 ctprf : LTE cur tot} ->
             (node : Node (MkNodeCfg clustSize') (MkNodeArgs cur tot @{ctprf}) Blobful Rootful) ->
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
    
    -- when bdata.onlyOneFat $ do
    --     serializeNode node 0 0 names cmap (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)) (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec) + 8) image @{%search} @{reflexive} @{ do
    --         rewrite bdata.csPrf
    --         replace {p = \x => LTE x tsz} ((bdata.sizePrf `trans` plusAssociative _ _ _) `trans` cong (\x => (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + x * bdata.clustSize)) (sym bdata.tclsPrf)) reflexive
    --     } @{ CalcSmart $
    --         |~ bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec) + 8 + (tcls * 4)
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec) + 8 + (bdata.dataClust * 4)
    --             ... cong (\x => bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec) + 8 + (x * 4)) bdata.tclsPrf
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec) + (8 + bdata.dataClust * 4)
    --             ..< plusAssociative _ _ _
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec) + (bdata.fatSz * bdata.bytsPerSec)
    --             ..> plusLteMonotoneLeft _ _ _ (bdataFatPrf bdata)
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)
    --             ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) (finToNat bdata.activeFat) (bdata.fatSz * bdata.bytsPerSec)
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
    --             ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S $ finToNat bdata.activeFat) bdata.numFats (bdata.fatSz * bdata.bytsPerSec) (elemSmallerThanBound bdata.activeFat))
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
    --             ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
    --             ..< plusAssociative _ _ _ 
    --         ~~ tsz
    --             ..< bdata.sizePrf
    --     }
    --     lift1 $ icopy fat0 0 (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)) 4 @{%search} @{ CalcSmart $
    --         |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)) + 4
    --         <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)) + (8 + bdata.dataClust * 4)
    --             ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)) 4 (8 + bdata.dataClust * 4) (lteAddRight 4)
    --         <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)) + (bdata.fatSz * bdata.bytsPerSec)
    --             ..> plusLteMonotoneLeft _ _ _ (bdataFatPrf bdata)
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)
    --             ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) (finToNat bdata.activeFat) (bdata.fatSz * bdata.bytsPerSec)
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
    --             ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S $ finToNat bdata.activeFat) bdata.numFats (bdata.fatSz * bdata.bytsPerSec) (elemSmallerThanBound bdata.activeFat))
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
    --             ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
    --             ..< plusAssociative _ _ _ 
    --         ~~ tsz
    --             ..< bdata.sizePrf
    --     } image
    --     lift1 $ icopy fat1 0 ((bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)) + 4) 4 @{%search} @{ CalcSmart $
    --         |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec))) + 4 + 4
    --         ~~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec))) + 8
    --             ..< plusAssociative _ _ _
    --         <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec))) + (8 + bdata.dataClust * 4)
    --             ..> plusLteMonotoneLeft ((bdata.rsvdSecCnt * bdata.bytsPerSec) + (finToNat (bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec))) 8 (8 + bdata.dataClust * 4) (lteAddRight 8)
    --         <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (finToNat (bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec))) + (bdata.fatSz * bdata.bytsPerSec)
    --             ..> plusLteMonotoneLeft _ _ _ (bdataFatPrf bdata)
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + finToNat bdata.activeFat) * (bdata.fatSz * bdata.bytsPerSec)
    --             ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) (finToNat bdata.activeFat) (bdata.fatSz * bdata.bytsPerSec)
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
    --             ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S $ finToNat bdata.activeFat) bdata.numFats (bdata.fatSz * bdata.bytsPerSec) (elemSmallerThanBound bdata.activeFat))
    --         <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
    --             ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
    --         ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
    --             ..< plusAssociative _ _ _ 
    --         ~~ tsz
    --             ..< bdata.sizePrf
    --     } image
    when (not bdata.onlyOneFat) $ do
        serializeNode node 0 0 names cmap (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)) (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec) + 8) image @{%search} @{reflexive} @{ do
            rewrite bdata.csPrf
            replace {p = \x => LTE x tsz} ((bdata.sizePrf `trans` plusAssociative _ _ _) `trans` cong (\x => (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + x * bdata.clustSize)) (sym bdata.tclsPrf)) reflexive
        } @{ CalcSmart $
            |~ bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec) + 8 + (tcls * 4)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec) + 8 + (bdata.dataClust * 4)
                ... cong (\x => bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec) + 8 + (x * 4)) bdata.tclsPrf
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec) + (8 + bdata.dataClust * 4)
                ..< plusAssociative _ _ _
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec) + (bdata.fatSz * bdata.bytsPerSec)
                ..> plusLteMonotoneLeft _ _ _ (bdataFatPrf bdata)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (bdata.fatSz * bdata.bytsPerSec)
                ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 (bdata.fatSz * bdata.bytsPerSec)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (bdata.fatSz * bdata.bytsPerSec) bdata.nfatsPrf)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        }
        lift1 $ icopy fat0 0 (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec)) 4 @{%search} @{ CalcSmart $
            |~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (bdata.fatSz * bdata.bytsPerSec)) + 4
            <~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (bdata.fatSz * bdata.bytsPerSec)) + (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (bdata.fatSz * bdata.bytsPerSec)) 4 (8 + bdata.dataClust * 4) (lteAddRight 4)
            <~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (bdata.fatSz * bdata.bytsPerSec)) + (bdata.fatSz * bdata.bytsPerSec)
                ..> plusLteMonotoneLeft _ _ _ (bdataFatPrf bdata)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (bdata.fatSz * bdata.bytsPerSec)
                ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 (bdata.fatSz * bdata.bytsPerSec)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (bdata.fatSz * bdata.bytsPerSec) bdata.nfatsPrf)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        } image
        lift1 $ icopy fat1 0 ((bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec)) + 4) 4 @{%search} @{ CalcSmart $
            |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec)) + 4 + 4
            ~~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec)) + 8
                ..< plusAssociative _ _ _
            <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec)) + (8 + bdata.dataClust * 4)
                ..> plusLteMonotoneLeft ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (bdata.fatSz * bdata.bytsPerSec)) 8 (8 + bdata.dataClust * 4) (lteAddRight 8)
            <~ (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec)) + (bdata.fatSz * bdata.bytsPerSec)
                ..> plusLteMonotoneLeft _ _ _ (bdataFatPrf bdata)
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (bdata.fatSz * bdata.bytsPerSec)
                ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 (bdata.fatSz * bdata.bytsPerSec)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
                ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (bdata.fatSz * bdata.bytsPerSec) bdata.nfatsPrf)
            <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
                ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
            ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
                ..< plusAssociative _ _ _ 
            ~~ tsz
                ..< bdata.sizePrf
        } image
        for_ (boundedRangeLT 1 bdata.numFats @{bdata.nfatsPrf}) $ \(Element f fp) => do
            lift1 $ copy image
                (bdata.rsvdSecCnt * bdata.bytsPerSec + 0 * (bdata.fatSz * bdata.bytsPerSec))
                (bdata.rsvdSecCnt * bdata.bytsPerSec + f * (bdata.fatSz * bdata.bytsPerSec))
                (bdata.fatSz * bdata.bytsPerSec) image 
                @{ CalcSmart $
                    |~ ((bdata.rsvdSecCnt * bdata.bytsPerSec) + 0 * (bdata.fatSz * bdata.bytsPerSec)) + (bdata.fatSz * bdata.bytsPerSec)
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + 1 * (bdata.fatSz * bdata.bytsPerSec)
                        ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) 0 (bdata.fatSz * bdata.bytsPerSec)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
                        ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft 1 bdata.numFats (bdata.fatSz * bdata.bytsPerSec) bdata.nfatsPrf)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
                        ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
                        ..< plusAssociative _ _ _ 
                    ~~ tsz
                        ..< bdata.sizePrf
                }
                @{ CalcSmart $
                    |~ (bdata.rsvdSecCnt * bdata.bytsPerSec + (f * (bdata.fatSz * bdata.bytsPerSec))) + (bdata.fatSz * bdata.bytsPerSec)
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (1 + f) * (bdata.fatSz * bdata.bytsPerSec)
                        ... eqPrf4 (bdata.rsvdSecCnt * bdata.bytsPerSec) f (bdata.fatSz * bdata.bytsPerSec)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec)
                        ..> plusLteMonotoneLeft (bdata.rsvdSecCnt * bdata.bytsPerSec) _ _ (multLteMonotoneLeft (S f) bdata.numFats (bdata.fatSz * bdata.bytsPerSec) fp)
                    <~ bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize
                        ..> lteAddRight (bdata.rsvdSecCnt * bdata.bytsPerSec + bdata.numFats * (bdata.fatSz * bdata.bytsPerSec))
                    ~~ bdata.rsvdSecCnt * bdata.bytsPerSec + (bdata.numFats * (bdata.fatSz * bdata.bytsPerSec) + bdata.dataClust * bdata.clustSize)
                        ..< plusAssociative _ _ _ 
                    ~~ tsz
                        ..< bdata.sizePrf
                }


-- public export
-- genImage : (fuel1 : Fuel) -> (fuel2 : Fuel) -> (cfg : NodeCfg) -> (minClust : Nat) -> Gen MaybeEmpty (Buffer, Int)
-- genImage fuel1 fuel2 (MkNodeCfg clustSize @{clustNZ}) minClust = do
--     (ar@(MkNodeArgs _ tot) ** node) <- genFilesystemB fuel1 $ MkNodeCfg clustSize
--     names <- genNameTree fuel2 (MkNodeCfg clustSize) ar True True node @{const genBits8} @{const genFilename}
--     let tcls : Nat
--         tcls = maximum 65525 $ maximum minClust tot
--     let tclsPrf = maximumRightUpperBound minClust tot `transitive` maximumRightUpperBound 65525 (maximum minClust tot)
--     let genvect = 
--             case isItSucc tot of
--                 (Yes prf) => replace {p = \t => Gen MaybeEmpty (Vect tot (Fin t))} (plusCommutative tot (tcls `minus` tot) `trans` plusMinusLte tot tcls tclsPrf) $ genMap tot (tcls `minus` tot)
--                 (No contra)    => case tot of
--                                        0 => pure []
--                                        (S k) => void $ contra ItIsSucc
--     cvect <- genvect
--     let cmap = array cvect
--     let root = 
--         case isLT 0 tot of
--           (Yes prf) => 2 + finToNat (atNat cmap 0 @{prf})
--           (No _)    => 2
--     (tsz ** bdata) <- genBootSectorData clustSize tcls root
--     bsect <- genBootSector bdata
--     fsinfo <- genFsInfo tcls
--     pure $ runPure $ do
--         image <- mbuffer tsz
--         buildImage bdata bsect fsinfo node names cmap image
--         pure $ (unsafeFromMBuffer image, cast tsz)

public export
genImageIO : (seed : Bits64) -> (fuel1 : Fuel) -> (fuel2 : Fuel) -> (cfg : NodeCfg) -> (minClust : Nat) -> Bool -> Bool -> Bool -> IO (Buffer, Int)
genImageIO seed fuel1 fuel2 (MkNodeCfg clustSize @{clustNZ}) minClust printNode printNodeB printNames = do
    putStrLn "generating Node..."
    let (Just (ar@(MkNodeArgs cur tot) ** node)) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ genFilesystem fuel1 $ MkNodeCfg clustSize
        | Nothing => die "failed to generate Node"
    when printNode $ printLn node
    putStrLn "generating NodeB..."
    let (Just nodeb) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ fillBlobs node
        | Nothing => die "failed to generate NodeB"
    when printNodeB $ printLn nodeb
    putStrLn "generating NameTree..."
    let (Just names) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ genNameTree fuel2 (MkNodeCfg clustSize) (MkNodeArgs cur tot) Blobful Rootful nodeb @{const genBits8} @{const genFilename}
        | Nothing => die "failed to generate NameTree"
    when printNames $ printLn names
    let tcls : Nat
        tcls = maximum 65525 $ maximum minClust tot
    let tclsPrf = maximumRightUpperBound minClust tot `transitive` maximumRightUpperBound 65525 (maximum minClust tot)
    let genvect = 
            case isItSucc tot of
                (Yes prf) => replace {p = \t => Gen MaybeEmpty (Vect tot (Fin t))} (plusCommutative tot (tcls `minus` tot) `trans` plusMinusLte tot tcls tclsPrf) $ genMap tot (tcls `minus` tot)
                (No contra)    => case tot of
                                       0 => pure []
                                       (S k) => void $ contra ItIsSucc
    putStrLn "generating cmap..."
    let (Just cvect) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ genvect
        | Nothing => die "failed to generate cmap"
    let cmap = array cvect
    let root = 
        case isLT 0 tot of
          (Yes prf) => 2 + finToNat (atNat cmap 0 @{prf})
          (No _)    => 2
    putStrLn "generating bdata..."
    let (Just (tsz ** bdata)) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ genBootSectorData clustSize tcls root
        | Nothing => die "failed to generate bdata"
    putStrLn "generating bsect..."
    let (Just bsect) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ genBootSector bdata
        | Nothing => die "failed to generate bsect"
    putStrLn "generating fsinfo..."
    let (Just fsinfo) = runIdentity $ pick @{ConstSeed $ mkStdGen seed} $ genFsInfo tcls
        | Nothing => die "failed to generate fsinfo"
    putStrLn "building the image..."
    pure $ runPure $ do
        image <- mbuffer tsz
        buildImage bdata bsect fsinfo nodeb names cmap image
        pure $ (unsafeFromMBuffer image, cast tsz)

