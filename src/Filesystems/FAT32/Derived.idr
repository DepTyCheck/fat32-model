module Filesystems.FAT32.Derived

import public Filesystems.FAT32
import public Deriving.DepTyCheck.Gen

%default total

%logging "deptycheck.derive" 5

Filesystems.FAT32.genFilesystem = deriveGen

-- genFinInc : Fuel -> Gen MaybeEmpty (n ** FinInc n)
-- genFinInc = deriveGen

