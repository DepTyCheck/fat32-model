module Filesystems.FAT32.Gen

import Filesystems.FAT32

%default total
%hide Data.Nat.divCeilNZ
%language ElabReflection
%prefix_record_projections off

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
genBlob : (blobLimit : Nat) -> Gen MaybeEmpty (k ** SnocVectBits8 k)
genBlob blobLimit = do
  k <- elements' $ the (List Nat) [0..blobLimit]
  blob <- genSnocVectBits8 k
  pure (k ** blob)

-- public export
-- genUniqNames : Fuel ->
--                (Fuel -> Gen MaybeEmpty Filename) =>
--                (cfg : NodeCfg) ->
--                (k : Nat) ->
--                (ars : SnocVectNodeArgs k) ->
--                (sx : HSnocVectMaybeNode cfg k ars) ->
--                Gen MaybeEmpty $ UniqNames {cfg} {k} {ars} sx

public export
genNode : Fuel -> 
          (Fuel -> Gen MaybeEmpty (k ** SnocVectBits8 k)) => 
          (Fuel -> Gen MaybeEmpty Filename) =>
          (cfg : NodeCfg) -> 
          (fs : RootLabel) -> 
          Gen MaybeEmpty (ar ** Node cfg ar fs)

public export
genFilesystem : Fuel -> (cfg : NodeCfg) -> (blobLimit : Nat) -> Gen MaybeEmpty (ar ** Filesystem cfg ar)
genFilesystem fuel cfg blobLimit = genNode fuel @{const $ genBlob blobLimit} @{%search} cfg Rootful

-- fillBlobs' : MaybeNode cfg ar Blobless nm Rootless -> Gen MaybeEmpty $ MaybeNode cfg ar Blobful nm Rootless
-- fillBlobs' Nothing = pure Nothing
-- fillBlobs' (Just $ Dir meta names entries) = Just <$> Dir meta names <$> assert_total (traverse' fillBlobs' entries)
-- fillBlobs' (Just $ File meta _ {k}) = Just <$> File meta <$> BlobSome <$> genSnocVectBits8 k
--
-- public export
-- fillBlobs : Node cfg ar Blobless nm Rootful -> Gen MaybeEmpty $ Node cfg ar Blobful nm Rootful
-- fillBlobs (Root names entries) = Root names <$> (traverse' fillBlobs' entries)

-- fillNames' : Fuel -> 
--              MaybeNode cfg ar Nameless Rootless -> 
--              Gen MaybeEmpty $ MaybeNode cfg ar Nameful Rootless
-- fillNames' _ Nothing = pure Nothing
-- fillNames' _ (Just (File meta x)) = pure $ Just $ File meta x
-- fillNames' fuel (Just (Dir meta _ entries {k})) = pure $ Just $ Dir meta (NamesSome !(genUniqNames fuel k)) !(assert_total $ traverse' (fillNames' fuel) entries)
--
-- public export
-- fillNames : Fuel -> 
--             Node cfg ar Nameless Rootful -> 
--             Gen MaybeEmpty $ Node cfg ar Nameful Rootful
-- fillNames fuel (Root _ entries {k}) = pure $ Root (NamesSome !(genUniqNames fuel k)) !(traverse' (fillNames' fuel) entries) 
