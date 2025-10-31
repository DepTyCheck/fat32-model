module Filesystems.FAT32.Derived.NameTree

import Filesystems.FAT32
import Filesystems.FAT32.NameTree
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Filesystems.FAT32.NameTree.genNameTree = deriveGen
