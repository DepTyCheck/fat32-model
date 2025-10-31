module Filesystems.FAT32.NodeOps

import Filesystems.FAT32
import Filesystems.FAT32.NameTree
import Filesystems.FAT32.Index

%default total
%prefix_record_projections off

-- TODO: Ponder if IndexIn should be indexed by Node or MaybeNode
-- TODO: Fix IndexIn to point only at Dir/Root (as in, possible insertion place for a file), possibly create a separate type for that (or index this one by a Bool)

-- setFlags : (node : Node cfg ar wb fs) -> IndexIn node NonRoot dirl -> Metadata -> Node cfg ar wb fs
-- setFlags node idx meta = ?setFlags_rhs
--
-- public export
-- data NodeOps : (node : Node cfg ar True True) -> NameTree node -> Type where
--     Stat : (idx : IndexIn node NonRoot _) ->
--            NodeOps node tree
--     SetFlags : (idx : IndexIn node NonRoot _) ->
--                (meta : Metadata) ->
--                NodeOps (setFlags node idx meta) tree


    -- NewFile : (name : Filename) ->
    --           (blob : VectBits8 k) ->
    --           (idx : IndexIn node) ->
    --           (cont : Node _ _ _ _) ->
    --           NodeOps node

