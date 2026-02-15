module Filesystems.FAT32.Pretty

import Filesystems.FAT32
import Data.SnocVect
import Data.Nat.Views

%default total
%hide Data.Nat.divCeilNZ
%language ElabReflection
%prefix_record_projections off

data AbstractPrintableNode : Type where
  File : (meta : Metadata) -> (blob : SnocVect k Bits8) -> AbstractPrintableNode
  Dir : (meta : Metadata) -> (ents : List (AbstractPrintableNode, String)) -> AbstractPrintableNode

convertBlob : SnocVectBits8 k -> SnocVect k Bits8
convertBlob [<] = [<]
convertBlob (x :< m) = convertBlob x :< m

convertEnts : HSnocVectMaybeNode cfg k ars prs -> UniqNames prs -> List (AbstractPrintableNode, String) -> List (AbstractPrintableNode, String)

convertNode : Node cfg ar rootl -> AbstractPrintableNode
convertNode (File meta blob) = File meta $ convertBlob blob
convertNode (Dir meta ents names) = Dir meta (convertEnts ents names [])
convertNode (Root ents names) = Dir (MkMetadata False False False False) (convertEnts ents names [])

convertEnts [<] Empty acc = acc
convertEnts (x :< Nothing) (NewName ff Nothing) acc = convertEnts x ff acc
convertEnts (x :< (Just y)) (NewName ff (Just f)) acc = convertEnts x ff ((convertNode y, "\{f}") :: acc)

sortNode : AbstractPrintableNode -> AbstractPrintableNode
sortNode nd@(File meta blob) = nd
sortNode (Dir meta ents) = assert_total $ Dir meta (mapFst sortNode <$> sortBy (\x, y => snd x `compare` snd y) ents)

printEnts : (pref : String) -> (ents : List (AbstractPrintableNode, String)) -> String

printNode : String -> AbstractPrintableNode -> String
printNode pref (File meta blob) = ""
printNode pref (Dir meta ents) = printEnts pref ents

printEnts pref [] = ""
printEnts pref ((node, f) :: []) = pref ++ "└── \{f}\n" ++ printNode (pref ++ "    ") node
printEnts pref ((node, f) :: xs) = pref ++ "├── \{f}\n" ++ printNode (pref ++ "│   ") node ++ printEnts pref xs

public export
printTree : Node cfg ar Rootful -> String
printTree node = printNode "" $ sortNode $ convertNode node
