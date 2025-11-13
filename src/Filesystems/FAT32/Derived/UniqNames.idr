module Filesystems.FAT32.Derived.UniqNames

import Filesystems.FAT32
import Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Filesystems.FAT32.genUniqNames = deriveGen

