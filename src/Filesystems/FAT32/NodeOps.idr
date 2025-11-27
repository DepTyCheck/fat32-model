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
addDir : (cfg : NodeCfg) ->
         (node : Node cfg (MkNodeArgs cur tot @{lprf}) wb Nameful Rootful) ->
         (idx : IndexIn node rootl DirI) ->
         Metadata ->
         (name : Filename) ->
         (nameprf : uncurry NameIsNew .| namesGet node idx .| name) ->
         Node cfg (case idx of
           HereRoot => MkNodeArgs (cur + DirentSize) (tot + 3 * DirentSize) @{ CalcSmart $
             |~ cur + DirentSize
             <~ tot + DirentSize
               ..> plusLteMonotoneRight _ _ _ lprf
             <~ (tot + DirentSize) + 2 * DirentSize
               ..> lteAddRight _
             ~~ tot + 3 * DirentSize
               ..< plusAssociative _ _ _
           }
           _ => MkNodeArgs cur (tot + 3 * DirentSize) @{lprf `transitive` lteAddRight tot}
         ) wb Nameful Rootful
addDir cfg node idx x name nameprf = ?addDir_rhs
-- TODO: implement addDir
-- ponder if indexUpd should be generalized somehow to allow for fully type-level NodeArgs updating (throughout the whole path upwards to the root)



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
               (meta : Metadata) ->
               (name : Filename) ->
               (nameprf : uncurry NameIsNew .| namesGet node idx .| name) ->
               (cont : NodeOps cfg (addDir cfg node idx meta name nameprf)) ->
               NodeOps cfg {ar=MkNodeArgs cur tot @{lprf}} node

-- %runElab deriveIndexed "NodeOps" [Show]

public export
genNodeOps : Fuel ->
             (cfg : NodeCfg) ->
             (ar : NodeArgs) ->
             (node : Node cfg ar Blobful Nameful Rootful) ->
             Gen MaybeEmpty (NodeOps cfg node)


    -- NewFile : (name : Filename) ->
    --           (blob : VectBits8 k) ->
    --           (idx : IndexIn node) ->
    --           (cont : Node _ _ _ _) ->
    --           NodeOps node

