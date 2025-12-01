module Filesystems.FAT32.NodeOps

import Filesystems.FAT32
import Filesystems.FAT32.Index
import Derive.Prelude
import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
import Syntax.IHateParens


%default total
%prefix_record_projections off
%language ElabReflection
%hide Data.Nat.divCeilNZ


public export
setFlags : (cfg : NodeCfg) -> (node : Node cfg ar wb nm fs) -> IndexIn node Rootless dirl -> Metadata -> Node cfg ar wb nm fs
setFlags cfg@(MkNodeCfg clustSize) node idx meta = indexUpd_ cfg node idx f
where f : Node cfg ar1 wb nm Rootless -> Node cfg ar1 wb nm Rootless
      f (File _ blob) = File meta blob
      f (Dir _ names entries) = Dir meta names entries

public export
namesGet : (node : Node cfg ar wb Nameful Rootful) -> (idx : IndexIn node rootl DirI) -> (k ** UniqNames k)
namesGet node idx {ar} with (indexGet node idx)
  _ | (Evidence _ ((Dir _ (NamesSome names) _ ** _))) = (_ ** names)
  _ | (Evidence _ ((Root (NamesSome names) _ ** _))) = (_ ** names)
  namesGet (Root {ars} names xs) (ThereRoot x) {ar=MkNodeArgs _ (_ + totsum ars)} | (Evidence _ ((File {} ** ati'))) = void $ uninhabited ati'

public export
newDir : (cfg : NodeCfg) ->
         (node : Node cfg ar wb Nameful Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         (name : Filename) ->
         (nameprf : uncurry NameIsNew .| namesGet node idx .| name) ->
         (ar' ** Node cfg ar' wb Nameful Rootful)
newDir cfg@(MkNodeCfg clusterSize) node idx name nameprf {ar} with (indexGet node idx)
  _ | (Evidence _ ((Dir meta' (NamesSome names') sx' ** _))) = indexSet (MkNodeCfg _) node idx (Dir meta' (NamesSome $ NewName @{names'} name @{nameprf}) (sx' :< Just (Dir (MkMetadata False False False False) (NamesSome Empty) [<])))
  _ | (Evidence _ ((Root (NamesSome names') sx' ** _))) = indexSet (MkNodeCfg _) node idx (Root (NamesSome $ NewName @{names'} name @{nameprf}) (sx' :< Just (Dir (MkMetadata False False False False) (NamesSome Empty) [<])))
  newDir (MkNodeCfg _) (Root {ars} names xs) (ThereRoot x) _ _ {ar=MkNodeArgs _ (_ + totsum ars)} | (Evidence _ ((File {} ** ati'))) = void $ uninhabited ati'

public export
newFile : (cfg : NodeCfg) ->
          (node : Node cfg ar Blobful Nameful Rootful) ->
          (idx : IndexIn node rootl DirI) ->
          (name : Filename) ->
          (nameprf : uncurry NameIsNew .| namesGet node idx .| name) ->
          (ar' ** Node cfg ar' Blobful Nameful Rootful)
newFile cfg@(MkNodeCfg clusterSize) node idx name nameprf {ar} with (indexGet node idx)
  _ | (Evidence _ ((Dir meta' (NamesSome names') sx' ** _))) = indexSet (MkNodeCfg _) node idx (Dir meta' (NamesSome $ NewName @{names'} name @{nameprf}) (sx' :< Just (File (MkMetadata False False False False) (BlobSome [<]))))
  _ | (Evidence _ ((Root (NamesSome names') sx' ** _))) = indexSet (MkNodeCfg _) node idx (Root (NamesSome $ NewName @{names'} name @{nameprf}) (sx' :< Just (File (MkMetadata False False False False) (BlobSome [<]))))
  newFile (MkNodeCfg _) (Root {ars} names xs) (ThereRoot x) _ _ {ar=MkNodeArgs _ (_ + totsum ars)} | (Evidence _ ((File {} ** ati'))) = void $ uninhabited ati'

public export
data NodeOps : (cfg : NodeCfg) -> (node : Node cfg ar Blobful Nameful Rootful) -> Type where
    Nop : NodeOps cfg node
    GetFlags : (idx : IndexIn node rootl dirl) ->
               (cont : NodeOps cfg node) ->
               NodeOps cfg node
    SetFlags : (idx : IndexIn node Rootless dirl) ->
               (meta : Metadata) ->
               (cont : NodeOps cfg (setFlags cfg node idx meta)) ->
               NodeOps cfg node
    NewDir   : (idx : IndexIn node rootl DirI) ->
               (name : Filename) ->
               (nameprf : uncurry NameIsNew .| namesGet node idx .| name) ->
               (cont : NodeOps cfg (snd $ newDir cfg node idx name nameprf)) ->
               NodeOps cfg node
    NewFile  : (idx : IndexIn node rootl DirI) ->
               (name : Filename) ->
               (nameprf : uncurry NameIsNew .| namesGet node idx .| name) ->
               (cont : NodeOps cfg (snd $ newFile cfg node idx name nameprf)) ->
               NodeOps cfg node

public export
length : NodeOps cfg node -> Nat
length Nop = 0
length (GetFlags idx cont) = S $ length cont
length (SetFlags idx meta cont) = S $ length cont
length (NewDir idx name nameprf cont) = S $ length cont
length (NewFile idx name nameprf cont) = S $ length cont

-- %runElab deriveIndexed "NodeOps" [Show]

public export
genNodeOps : Fuel ->
             (Fuel -> Gen MaybeEmpty Bits8) => 
             (Fuel -> Gen MaybeEmpty Filename) =>
             (cfg : NodeCfg) ->
             (ar : NodeArgs) ->
             (node : Node cfg ar Blobful Nameful Rootful) ->
             Gen MaybeEmpty (NodeOps cfg node)


    -- NewFile : (name : Filename) ->
    --           (blob : VectBits8 k) ->
    --           (idx : IndexIn node) ->
    --           (cont : Node _ _ _ _) ->
    --           NodeOps node

