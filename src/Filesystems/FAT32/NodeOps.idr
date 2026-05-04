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
newDir : (cfg : NodeCfg) ->
         (node : Node cfg ar Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         (name : Filename) ->
         (nameprf : NameIsNew (snd $ snd $ snd $ snd $ getContentsByDirIndex node idx) (Just name)) ->
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
          (nameprf : NameIsNew (snd $ snd $ snd $ snd $ getContentsByDirIndex node idx) (Just name)) ->
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
    _ | (_ ** Evidence _ (sp', Element ff' _)) = indexSet (MkNodeCfg _) node idx (Dir meta sp' ff')
  _ | (Evidence _ (Root sp ff ** _)) with (shallowIndexSet (MkNodeCfg _) _ _ sp ff sidx Nothing)
    _ | (_ ** Evidence _ (sp', Element ff' _)) = indexSet (MkNodeCfg _) node idx (Root sp' ff')

public export
mvNode : (cfg : NodeCfg) ->
         (node : Node cfg ar Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex node idx) ->
         (idx2 : IndexIn (snd $ rmNode cfg node idx sidx) rootl DirI) ->
         (name : Filename) ->
         (nameprf : NameIsNew (snd $ snd $ snd $ snd $ getContentsByDirIndex (DPair.snd $ rmNode cfg node idx sidx) idx2) (Just name)) ->
         (ar'' ** Node cfg ar'' Rootful)
mvNode (MkNodeCfg _) node idx sidx idx2 name nameprf {ar} with (compoundIndexGet _ _ sidx) | (indexGet (snd $ rmNode _ _ _ sidx) idx2)
  _ | _ | Evidence _ (File {} ** ati) = void $ uninhabited ati
  _ | (_ ** src) | Evidence _ (Dir meta sp ff ** _) = indexSet _ _ idx2 $ Dir meta .| sp :< Just src $ NewName ff $ Just name
  _ | (_ ** src) | Evidence _ (Root sp ff ** _) = indexSet _ _ idx2 $ Root .| sp :< Just src $ NewName ff $ Just name

public export
writeNode : (cfg : NodeCfg) ->
            {ar : NodeArgs} ->
            (root : Node cfg ar Rootful) ->
            (idx : IndexIn root Rootless FileI) ->
            (off : Nat) ->
            (len : Nat) ->
            (blob : VectBits8 len) ->
            (ar' ** Node cfg ar' Rootful)
writeNode (MkNodeCfg _) root idx off len blob with (indexGet root idx)
  _ | (Evidence _ (File meta sx ** _)) = if meta.readOnly then (_ ** root) else indexSet _ _ idx $ File meta $ overwriteAt sx off blob
  _ | (Evidence _ (Dir {} ** ati)) = void $ uninhabited ati

public export
data NodeOps : (cfg : NodeCfg) -> (root : Node cfg ar Rootful) -> Type where
    Nop : NodeOps cfg root
    GetFlags : (idx : IndexIn root rootl dirl) ->
               (cont : NodeOps cfg root) ->
               NodeOps cfg root
    SetFlags : (idx : IndexIn root Rootless dirl) ->
               (meta : Metadata) ->
               (cont : NodeOps cfg (setFlags cfg root idx meta)) ->
               NodeOps cfg root
    NewDir   : (idx : IndexIn root rootl DirI) ->
               (name : Filename) ->
               (nameprf : NameIsNew (snd $ snd $ snd $ snd $ getContentsByDirIndex root idx) (Just name)) ->
               (cont : NodeOps cfg (snd $ newDir cfg root idx name nameprf)) ->
               NodeOps cfg root
    NewFile  : (idx : IndexIn root rootl DirI) ->
               (name : Filename) ->
               (nameprf : NameIsNew (snd $ snd $ snd $ snd $ getContentsByDirIndex root idx) (Just name)) ->
               (cont : NodeOps cfg (snd $ newFile cfg root idx name nameprf)) ->
               NodeOps cfg root
    RmNode   : (idx : IndexIn root rootl DirI) ->
               (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex root idx) ->
               (cont : NodeOps cfg $ snd $ rmNode cfg root idx sidx) ->
               NodeOps cfg root
    MvNode   : (idx : IndexIn root rootl DirI) ->
               (sidx : ShallowIndexIn $ fst $ snd $ snd $ snd $ getContentsByDirIndex root idx) ->
               (idx2 : IndexIn (snd $ rmNode cfg root idx sidx) rootl DirI) ->
               (name : Filename) ->
               (nameprf : NameIsNew (snd $ snd $ snd $ snd $ getContentsByDirIndex (DPair.snd $ rmNode cfg root idx sidx) idx2) (Just name)) ->
               (cont : NodeOps cfg $ snd $ mvNode cfg root idx sidx idx2 name nameprf) ->
               NodeOps cfg root
    LsDir    : (idx : IndexIn root rootl DirI) ->
               (cont : NodeOps cfg root) ->
               NodeOps cfg root
    Read     : (idx : IndexIn root Rootless FileI) ->
               (src : Nat) ->
               (len : Nat) ->
               (lprf : LTE (src + len) $ fst $ getBlobByFileIndex root idx) ->
               (cont : NodeOps cfg root) ->
               NodeOps cfg root
    Write    : (idx : IndexIn root Rootless FileI) ->
               (off : Nat) ->
               (len : Nat) ->
               (blob : VectBits8 len) ->
               (cont : NodeOps cfg $ snd $ writeNode cfg root idx off len blob) ->
               NodeOps cfg root

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
length (Read _ _ _ _ cont)     = S $ length cont
length (Write _ _ _ _ cont)    = S $ length cont

-- %runElab deriveIndexed "NodeOps" [Show]

public export
genNodeOps : Fuel ->
             (Fuel -> Gen MaybeEmpty Filename) =>
             (Fuel -> Gen MaybeEmpty (k ** VectBits8 k)) => 
             (cfg : NodeCfg) ->
             (ar : NodeArgs) ->
             (root : Node cfg ar Rootful) ->
             Gen MaybeEmpty (NodeOps cfg root)
