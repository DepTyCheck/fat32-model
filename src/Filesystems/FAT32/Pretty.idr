module Filesystems.FAT32.Pretty

import Filesystems.FAT32
import Data.Buffer.Core
import Data.Array.Core
import Data.Array.Index
import Data.Array.Mutable
import Control.Monad.Pure
import Data.Bits

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

-- TODO: date and time generation
-- TODO: proper volume labels
makeDirent : {clustSize : Nat} -> (0 clustNZ : IsSucc clustSize) => Node (MkNodeCfg clustSize) (MkNodeArgs cur tot @{ctprf}) True False -> Filename -> (clustNum : Nat) -> VectBits8 DirentSize
makeDirent node fname cnum with (repr32' $ cast cnum)
    makeDirent (FileB meta x {k}) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ serializeMeta meta :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ repr32' (cast k)
    makeDirent (Dir meta entries) (MkFilename name) clustNum | (b0::b1::b2::b3::[]) = name ++ (serializeMeta meta .|. 0x10) :: replicate 8 0 ++ [b2, b3] ++ replicate 4 0 ++ [b0, b1] ++ replicate 4 0

-- TODO: work on erasability of LTE proofs in boundedRange' etc.
serializeNode : {clustSize : Nat} ->
                (0 clustNZ : IsSucc clustSize) =>
                {cur : Nat} ->
                {0 ctprf : LTE cur tot} ->
                (node : Node (MkNodeCfg clustSize) (MkNodeArgs cur tot @{ctprf}) True fs) ->
                (currClust : Nat) ->
                (names : NameTree node) ->
                (cmap : IArray cls (Fin tcls)) ->
                (dataOffset : Nat) ->
                (clsBounds : LTE (currClust + tot) cls) =>
                (tszBounds : LTE (dataOffset + tcls * clustSize) tsz) =>
                (image : MArray s tsz Bits8) ->
                Pure s ()
serializeNode (FileB meta blob {k}) currClust names cmap dataOffset image = do
    let pblob = padBlob clustSize clustNZ blob
    for_ (boundedRangeLT currClust (currClust + cur) @{lteAddRight currClust}) $ \(Element cl clp) => do
        let absclust = atNat cmap cl @{?aboba}
        ?ass
serializeNode (Dir meta entries) currClust names cmap dataOffset image = ?serializeNode_rhs_1
serializeNode (Root entries) currClust names cmap dataOffset image = ?serializeNode_rhs_2

