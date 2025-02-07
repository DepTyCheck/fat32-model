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
Cfg = MkNodeParams 32

-- vals = unGenTryN 1 (mkStdGen 9798294) (genFilesystem (limit 2) Cfg)
-- 1450272 4

aa : HVectMaybeNode' Cfg 2 [(MkNodeArgs 1 1 (MkFinInc 1 %search) (MkFinInc 1 %search)), (MkNodeArgs 1 1 (MkFinInc 1 %search) (MkFinInc 1 %search))]
aa = ?aaa

bb : HVectMaybeNode'' Cfg 2 [(MkNodeArgs 1 1 (MkFinInc 1 %search) (MkFinInc 1 %search)), (MkNodeArgs 1 1 (MkFinInc 1 %search) (MkFinInc 1 %search))]

main : IO ()
main = do
    (_::seed::lim::argv) <- getArgs
        | _ => putStrLn "incorrect input format"
    printLn $ runIdentity $ pick @{ConstSeed (mkStdGen (cast seed))} (genFilesystemS (limit (cast lim)) Cfg)

-- %logging "deptycheck.derive" 5
-- %language ElabReflection
-- %runElab deriveGenPrinter (Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust))
