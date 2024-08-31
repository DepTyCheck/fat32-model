module Main

import Data.Nat
import Data.Monomorphic.Vect
import Data.FinInc
import Filesystems.FAT32.Derived
import Gen1
import System.Random.Pure.StdGen


%default total

Cfg : NodeParams
Cfg = MkNodeParams 32 SIsNonZero

vals : LazyList (n ** Filesystem Cfg n)
vals = unGenTryN 1 (mkStdGen 9798294) (genFilesystem (limit 2) Cfg)

val1 : Maybe (n ** Filesystem Cfg n)
val1 = head' vals

main : IO ()
