module Filesystems.FAT32.NodeOps

import Filesystems.FAT32
import Filesystems.FAT32.Index
import Derive.Prelude


%default total
%prefix_record_projections off
%language ElabReflection

-- TODO: Ponder if IndexIn should be indexed by Node or MaybeNode
-- TODO: Fix IndexIn to point only at Dir/Root (as in, possible insertion place for a file), possibly create a separate type for that (or index this one by a Bool)

public export
setFlags : (cfg : NodeCfg) -> (node : Node cfg ar wb nm fs) -> IndexIn node Rootless dirl -> Metadata -> Node cfg ar wb nm fs
setFlags cfg@(MkNodeCfg clustSize) node idx meta = indexUpd_ cfg node idx f
where f : Node cfg ar1 wb nm Rootless -> Node cfg ar1 wb nm Rootless
      f (File _ blob) = File meta blob
      f (Dir _ names entries) = Dir meta names entries

public export
data NodeOps : (cfg : NodeCfg) -> (node : Node cfg ar Blobful Nameful Rootful) -> Type where
    Nop : NodeOps cfg node
    Stat : (idx : IndexIn node rootl dirl) ->
           (cont : NodeOps cfg node) ->
           NodeOps cfg node
    SetFlags : (idx : IndexIn node Rootless dirl) ->
               (meta : Metadata) ->
               (cont : NodeOps cfg (setFlags cfg node idx meta)) ->
               NodeOps cfg node

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

