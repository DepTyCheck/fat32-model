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
mvNode : (cfg : NodeCfg) ->
         (node : Node cfg ar Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex node idx) ->
         (idx2 : IndexIn (snd $ rmNode cfg node idx sidx) rootl DirI) ->
         (name : Filename) ->
         (nameprf : NameIsNew (snd $ snd $ namesGet (snd $ rmNode cfg node idx sidx) idx2) (Just name)) ->
         (ar'' ** Node cfg ar'' Rootful)
mvNode (MkNodeCfg _) node idx sidx idx2 name nameprf {ar} with (compoundIndexGet _ _ sidx) | (indexGet (snd $ rmNode _ _ _ sidx) idx2)
  _ | _ | Evidence _ (File {} ** ati) = void $ uninhabited ati
  _ | (_ ** src) | Evidence _ (Dir meta sp ff ** _) = indexSet _ _ idx2 $ Dir meta .| sp :< Just src $ NewName ff $ Just name
  _ | (_ ** src) | Evidence _ (Root sp ff ** _) = indexSet _ _ idx2 $ Root .| sp :< Just src $ NewName ff $ Just name

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
    MvNode   : (idx : IndexIn node rootl DirI) ->
               (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex node idx) ->
               (idx2 : IndexIn (snd $ rmNode cfg node idx sidx) rootl DirI) ->
               (name : Filename) ->
               (nameprf : NameIsNew (snd $ snd $ namesGet (snd $ rmNode cfg node idx sidx) idx2) (Just name)) ->
               (cont : NodeOps cfg $ snd $ mvNode cfg node idx sidx idx2 name nameprf) ->
               NodeOps cfg node
    LsDir    : (idx : IndexIn node rootl DirI) ->
               (cont : NodeOps cfg node) ->
               NodeOps cfg node

public export
length : NodeOps cfg node -> Nat
length Nop = 0
length (GetFlags _ cont)       = S $ length cont
length (SetFlags _ _ cont)     = S $ length cont
length (NewDir _ _ _ cont)     = S $ length cont
length (NewFile _ _ _ cont)    = S $ length cont
length (RmNode _ _ cont)       = S $ length cont
length (MvNode _ _ _ _ _ cont) = S $ length cont
length (LsDir _ cont)          = S $ length cont

-- %runElab deriveIndexed "NodeOps" [Show]

public export
genNodeOps : Fuel ->
             (Fuel -> Gen MaybeEmpty Bits8) => 
             (Fuel -> Gen MaybeEmpty Filename) =>
             (cfg : NodeCfg) ->
             (ar : NodeArgs) ->
             (node : Node cfg ar Rootful) ->
             Gen MaybeEmpty (NodeOps cfg node)
