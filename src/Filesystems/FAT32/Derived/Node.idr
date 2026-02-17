module Filesystems.FAT32.Derived.Node

import Filesystems.FAT32
import Filesystems.FAT32.Gen
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Filesystems.FAT32.Gen.genNode = deriveGen
