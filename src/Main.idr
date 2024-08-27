module Main

import Data.Nat
import Data.Monomorphic.Vect
import Data.FinInc
import Filesystems.FAT32.Derived

%default total

-- Cfg1 : FSConfig
-- Cfg1 = MkFSConfig (MkNodeParams 32 SIsNonZero) 4
--
-- exampleFilename1 : VectBits8 FilenameLength
--
-- %auto_implicit_depth 100
-- exampleContents1 : VectBits8 64
--
--
-- -- TODO: complete the example (?)
-- exampleFile1 : Node (Cfg1).nodeParams 3 3 (natToFinIncLTE 2) (natToFinIncLTE 2)
-- -- exampleFile1 = File (MkMetadata exampleFilename1 False False False False) exampleContents1 {k = (natToFinIncLTE 64)}
--
-- example : Filesystem Cfg1
-- example = Root [Just exampleFile1] {k = (natToFinIncLTE 1)} {n = 1}
--
