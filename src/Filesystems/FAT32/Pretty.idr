module Filesystems.FAT32.Pretty


import Filesystems.FAT32
import Data.Buffer.Core
import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Control.Monad.Pure
import Data.Bits
import Data.Fin.Properties

%default total

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
    makeDirent (Just $ FileB meta x {k}) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ serializeMeta meta :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ repr32' (cast k)
    makeDirent (Just $ Dir meta entries) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ (serializeMeta meta .|. 0x10) :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ replicate 4 0
    makeDirent Nothing _ _ | _ = emptyDirent


mapRangeWithNextVal : List (Subset Nat (`LT` b)) -> List (Subset Nat (`LT` b), Nat) 
mapRangeWithNextVal [] = []
mapRangeWithNextVal (x :: []) = [(x, 0)]
mapRangeWithNextVal (x :: (y@(Element fst snd) :: xs)) = (x, fst) :: mapRangeWithNextVal (y::xs)

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
            (image : MArray s tsz Bits8) ->
            Pure s ()
writeBlob clustSize' blob currClust cmap dataOffset fatOffset image = do
    let (BV blobBuf blobOff blobPrf) = packVect $ padBlob clustSize' clustNZ blob
    for_ (mapRangeWithNextVal $ boundedRangeLT 0 (divCeilNZ k clustSize')) $ forFile blobBuf blobOff blobPrf
    where forFile : IBuffer blen -> (boff : Nat) -> (0 bprf : LTE (boff + (divCeilNZ k clustSize') * clustSize') blen) -> (Subset Nat (`LT` divCeilNZ k clustSize'), Nat) -> Pure s ()
          forFile bbuf boff bprf (Element cl clp, nxt) = do
              let absclust : Fin tcls
                  absclust = atNat cmap (currClust + cl) @{
                      rewrite plusSuccRightSucc currClust cl
                      in plusLteMonotoneLeft currClust (S cl) (divCeilNZ k clustSize') clp
                              `transitive` clsBounds
                  }
              lift1 $ icopyToArray bbuf (boff + cl * clustSize') (dataOffset + finToNat absclust * clustSize') clustSize' image @{ do
                  rewrite sym $ plusAssociative boff (cl * clustSize') clustSize'
                  rewrite plusCommutative (cl * clustSize') clustSize'
                  (plusLteMonotoneLeft boff _ _ $ multLteMonotoneLeft (S cl) (divCeilNZ k clustSize') clustSize' clp) `transitive` bprf
              } @{ do
                  rewrite sym $ plusAssociative dataOffset (finToNat absclust * clustSize') clustSize'
                  rewrite plusCommutative (finToNat absclust * clustSize') clustSize'
                  (plusLteMonotoneLeft dataOffset _ _ $ multLteMonotoneLeft _ tcls clustSize' $ elemSmallerThanBound absclust) `transitive` tszBounds
              }
              let val = repr32'' $ cast nxt
              lift1 $ icopyToArray val 0 (fatOffset + finToNat absclust * 4) 4 image @{Relation.reflexive} @{do
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
                (image : MArray s tsz Bits8) ->
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
                        (image : MArray s tsz Bits8) ->
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


