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
setFlags : (cfg : NodeCfg) -> (node : Node cfg ar fs) -> IndexIn node Rootless dirl -> Metadata -> Node cfg ar fs
setFlags cfg@(MkNodeCfg clustSize) node idx meta = indexUpd_ cfg node idx f
where f : Node cfg ar1 Rootless -> Node cfg ar1 Rootless
      f (File _ blob) = File meta blob
      f (Dir _ entries names) = Dir meta entries names

public export
namesGet : (node : Node cfg ar Rootful) -> (idx : IndexIn node rootl DirI) -> (k ** prs ** UniqNames {k} prs)
namesGet node idx {ar} with (indexGet node idx)
  _ | (Evidence _ (Dir _ _ names ** _)) = (_ ** _ ** names)
  _ | (Evidence _ (Root _ names ** _)) = (_ ** _ ** names)
  _ | (Evidence _ (File _ _ ** ati')) = void $ uninhabited ati'

public export
newDir : (cfg : NodeCfg) ->
         (node : Node cfg ar Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         (name : Filename) ->
         (nameprf : NameIsNew (snd $ snd $ namesGet node idx) (Just name)) ->
         (ar' ** Node cfg ar' Rootful)
newDir cfg@(MkNodeCfg clusterSize) node idx name nameprf {ar} with (indexGet node idx)
  _ | (Evidence _ ((Dir meta' sx' names' ** _))) = indexSet (MkNodeCfg _) node idx (Dir meta' (sx' :< Just (Dir (MkMetadata False False False False) [<] Empty)) (NewName names' (Just name) @{nameprf}))
  _ | (Evidence _ ((Root sx' names' ** _))) = indexSet (MkNodeCfg _) node idx (Root (sx' :< Just (Dir (MkMetadata False False False False) [<] Empty)) (NewName names' (Just name) @{nameprf}))
  _ | (Evidence _ ((File {} ** ati'))) = void $ uninhabited ati'

public export
newFile : (cfg : NodeCfg) ->
          (node : Node cfg ar Rootful) ->
          (idx : IndexIn node rootl DirI) ->
          (name : Filename) ->
          (nameprf : NameIsNew (snd $ snd $ namesGet node idx) (Just name)) ->
          (ar' ** Node cfg ar' Rootful)
newFile cfg@(MkNodeCfg clusterSize) node idx name nameprf {ar} with (indexGet node idx)
  _ | (Evidence _ ((Dir meta' sx' names' ** _))) = indexSet (MkNodeCfg _) node idx (Dir meta' (sx' :< Just (File (MkMetadata False False False False) [<])) (NewName names' (Just name) @{nameprf}))
  _ | (Evidence _ ((Root sx' names' ** _))) = indexSet (MkNodeCfg _) node idx (Root (sx' :< Just (File (MkMetadata False False False False) [<])) (NewName names' (Just name) @{nameprf}))
  _ | (Evidence _ ((File {} ** ati'))) = void $ uninhabited ati'

public export
getContentsByDirIndex : (node : Node cfg ar Rootful) ->
                        (idx : IndexIn node rootl DirI) ->
                        (k ** ars ** prs ** (HSnocVectMaybeNode cfg k ars prs, UniqNames prs))
getContentsByDirIndex node idx with (indexGet node idx)
  _ | (Evidence _ (File {} ** ati)) = void $ uninhabited ati
  _ | (Evidence _ (Dir _ ents ff ** _)) = (_ ** _ ** _ ** (ents, ff))
  _ | (Evidence _ (Root ents ff ** _)) = (_ ** _ ** _ ** (ents, ff))

public export
rmNode : (cfg : NodeCfg) ->
         (node : Node cfg ar Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex node idx) ->
         (ar' ** Node cfg ar' Rootful)
rmNode (MkNodeCfg _) node idx sidx {ar} with (indexGet node idx)
  _ | (Evidence _ (File {} ** ati)) = void $ uninhabited ati
  _ | (Evidence _ (Dir meta sp ff ** _)) with (shallowIndexSet (MkNodeCfg _) _ _ sp ff sidx Nothing)
    _ | (_ ** _ ** (sp', Element ff' _)) = indexSet (MkNodeCfg _) node idx (Dir meta sp' ff')
  _ | (Evidence _ (Root sp ff ** _)) with (shallowIndexSet (MkNodeCfg _) _ _ sp ff sidx Nothing)
    _ | (_ ** _ ** (sp', Element ff' _)) = indexSet (MkNodeCfg _) node idx (Root sp' ff')

public export
data NodeOps : (cfg : NodeCfg) -> (node : Node cfg ar Rootful) -> Type where
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
               (nameprf : NameIsNew (snd $ snd $ namesGet node idx) (Just name)) ->
               (cont : NodeOps cfg (snd $ newDir cfg node idx name nameprf)) ->
               NodeOps cfg node
    NewFile  : (idx : IndexIn node rootl DirI) ->
               (name : Filename) ->
               (nameprf : NameIsNew (snd $ snd $ namesGet node idx) (Just name)) ->
               (cont : NodeOps cfg (snd $ newFile cfg node idx name nameprf)) ->
               NodeOps cfg node
    RmNode   : (idx : IndexIn node rootl DirI) ->
               (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex node idx) ->
               (cont : NodeOps cfg $ snd $ rmNode cfg node idx sidx) ->
               NodeOps cfg node

public export
length : NodeOps cfg node -> Nat
length Nop = 0
length (GetFlags idx cont) = S $ length cont
length (SetFlags idx meta cont) = S $ length cont
length (NewDir idx name nameprf cont) = S $ length cont
length (NewFile idx name nameprf cont) = S $ length cont
length (RmNode idx sidx cont) = S $ length cont

-- %runElab deriveIndexed "NodeOps" [Show]

public export
genNodeOps : Fuel ->
             (Fuel -> Gen MaybeEmpty Bits8) => 
             (Fuel -> Gen MaybeEmpty Filename) =>
             (cfg : NodeCfg) ->
             (ar : NodeArgs) ->
             (node : Node cfg ar Rootful) ->
             Gen MaybeEmpty (NodeOps cfg node)
