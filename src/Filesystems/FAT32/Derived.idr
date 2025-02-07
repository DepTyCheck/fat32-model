module Filesystems.FAT32.Derived

import public Filesystems.FAT32
import public Deriving.DepTyCheck.Gen

-- import PrintDerivation

%default total

%logging "deptycheck.derive" 5

-- Filesystems.FAT32.genFilesystem = deriveGen
Filesystems.FAT32.genFilesystemS = deriveGen

-- %language ElabReflection

-- genFilesystem = deriveGenFor (Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust))

