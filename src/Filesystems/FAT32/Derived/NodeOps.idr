module Filesystems.FAT32.Derived.NodeOps

import Filesystems.FAT32
import Filesystems.FAT32.Index
import public Filesystems.FAT32.NodeOps
import public Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Filesystems.FAT32.NodeOps.genNodeOps _ _ _ _ = pure Nop
