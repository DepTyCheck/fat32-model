module Filesystems.FAT32.Derived

import public Filesystems.FAT32
import Deriving.DepTyCheck.Gen
import public Data.List.Extra

%default total

%logging "deptycheck.derive" 5

Filesystems.FAT32.genFilesystem = deriveGen
