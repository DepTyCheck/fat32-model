module Main

import Data.Nat
import Data.Monomorphic.Vect
import Data.FinInc
import Filesystems.FAT32.Derived
-- import Gen1
import System.Random.Pure.StdGen
import System


%default total
%cg chez lazy=weakMemo


Cfg : NodeParams
Cfg = MkNodeParams 32 SIsNonZero

-- vals = unGenTryN 1 (mkStdGen 9798294) (genFilesystem (limit 2) Cfg)
-- 1450272 4

main : IO ()
main = do
    (_::seed::lim::argv) <- getArgs
        | _ => putStrLn "incorrect input format"
    printLn $ runIdentity $ pick @{ConstSeed (mkStdGen (cast seed))} (genFilesystem (limit (cast lim)) Cfg)

-- %logging "deptycheck.derive" 5
-- %language ElabReflection
-- %runElab deriveGenPrinter (Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust))
