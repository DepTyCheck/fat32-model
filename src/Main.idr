module Main

import Data.Nat
import Data.Monomorphic.Vect
import Data.FinInc
import Filesystems.FAT32.Derived
import System.Random.Pure.StdGen
import System
import System.GetOpts
import Derive.Prelude
import Derive.Barbie
import Control.Barbie

%default total
%language ElabReflection


record Config (m : Type -> Type) where
    constructor MkConfig
    params     : m NodeParams
    fuel     : m Fuel
    seed     : m Bits64
    printGen : m Bool
    help     : m Bool

%runElab derive "Config" [Barbie]

emptyCfg : Config Maybe
emptyCfg = MkConfig
    { params     = Nothing
    , fuel     = Nothing
    , seed     = Nothing
    , printGen = Nothing
    , help     = Nothing
    }

Cfg : Type
Cfg = Config Prelude.id

defaultCfg : Cfg
defaultCfg = MkConfig
    { params     = MkNodeParams 32
    , fuel     = limit 10
    , seed     = 1450262 
    , printGen = True
    , help     = False
    }

parseNat : String -> Either String Nat
parseNat = (maybeToEither "not a natural number") . parsePositive

parseFuel : String -> Either String $ Config Maybe
parseFuel s = pure $ {fuel := Just $ limit !(parseNat s)} emptyCfg

parseSeed : String -> Either String $ Config Maybe
parseSeed s = pure $ {seed := Just $ cast !(parseNat s)} emptyCfg

parseNodeParams : String -> Either String $ Config Maybe
parseNodeParams str with (parsePositive {a = Nat} str)
    _ | (Just x) with (isItSucc x)
      _ | (Yes prf) = Right $ {params := (Just $ MkNodeParams x)} emptyCfg
      _ | (No contra) = Left "0 is not a positive natural number"
    _ | Nothing = Left "not a natural number"

optDescs : List $ OptDescr $ Config Maybe
optDescs = [ MkOpt ['c'] ["cluster-size"] (ReqArg' parseNodeParams "<size>") "cluster size in bytes"
       , MkOpt ['f'] ["fuel"] (ReqArg' parseFuel "<fuel>") "fuel for the generator"
       , MkOpt ['s'] ["seed"] (ReqArg' parseSeed "<seed>") "seed"
       , MkOpt ['q'] ["quiet", "no-print"] (NoArg $ {printGen := Just False} emptyCfg) "don't print the generated value"
       , MkOpt ['h'] ["help"] (NoArg $ {help := Just True} emptyCfg) "print usage information"
       ]

-- main : IO ()
-- main = do
--     (_::clustSize::seed::lim::argv) <- getArgs
--         | _ => putStrLn "incorrect input format"
--     printLn $ runIdentity $ pick @{ConstSeed (mkStdGen (cast seed))} (genFilesystem (limit (cast lim)) Cfg)

main : IO ()
main = do
    let usage : Lazy String := usageInfo "Usage:" optDescs
    args <- fromMaybe [] <$> tail' <$> getArgs
    let MkResult {options, nonOptions, unrecognized, errors} := getOpt Permute optDescs args
    when (isCons nonOptions || isCons unrecognized) $ die "unrecognized options \{show $ nonOptions ++ unrecognized}\n\{usage}"
    when (isCons errors) $ die "parsing errors \{show errors}\n\{usage}"
    let cfg : Config Maybe := foldl (bzipWith (\x, y => x <|> y)) emptyCfg options
    let cfg : Cfg := bzipWith (\d, m => fromMaybe d m) defaultCfg cfg
    when cfg.help $ do
        putStrLn usage
        exitSuccess
    let val := runIdentity $ pick @{ConstSeed $ mkStdGen cfg.seed} (genFilesystem cfg.fuel cfg.params)
    when cfg.printGen $ printLn val
    

-- %logging "deptycheck.derive" 5
-- %language ElabReflection
-- %runElab deriveGenPrinter (Fuel -> (cfg : NodeParams) -> Gen MaybeEmpty (maxClust ** Filesystem cfg maxClust))
