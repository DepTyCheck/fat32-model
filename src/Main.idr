module Main

import Data.Nat
import Data.Monomorphic.Vect
import Filesystems.FAT32.Pretty
import Filesystems.FAT32.Derived.Node
import Filesystems.FAT32.Derived.NameTree
import Data.UniqFinVect
import Data.UniqFinVect.Derived
import System.Random.Pure.StdGen
import System
import System.GetOpts
import Derive.Prelude
import Derive.Barbie
import Control.Barbie
import Data.Buffer
import System.File.Buffer

%default total
%cg chez lazy=weakMemo
%language ElabReflection


record Config (m : Type -> Type) where
    constructor MkConfig
    params   : m NodeCfg
    fuel1   : m Fuel
    fuel2    : m Fuel
    fuel3    : m Fuel
    seed     : m Bits64
    minClust : m Nat
    -- printGen : m Bool
    output   : m String
    help     : m Bool

%runElab derive "Config" [Barbie]

emptyCfg : Config Maybe
emptyCfg = MkConfig
    { params   = Nothing
    , fuel1    = Nothing
    , fuel2    = Nothing
    , fuel3    = Nothing
    , seed     = Nothing
    , minClust = Nothing
    -- , printGen = Nothing
    , output   = Nothing
    , help     = Nothing
    }

Cfg : Type
Cfg = Config Prelude.id

defaultCfg : Cfg
defaultCfg = MkConfig
    { params   = MkNodeCfg 32
    , fuel1    = limit 10
    , fuel2    = limit 10
    , fuel3    = limit 10
    , seed     = 1450262
    , minClust = 0
    -- , printGen = True
    , output   = "out.img"
    , help     = False
    }

parseNat : String -> Either String Nat
parseNat = (maybeToEither "not a natural number") . parsePositive

parseFuel1 : String -> Either String $ Config Maybe
parseFuel1 s = pure $ {fuel1 := Just $ limit !(parseNat s)} emptyCfg

parseFuel2 : String -> Either String $ Config Maybe
parseFuel2 s = pure $ {fuel2 := Just $ limit !(parseNat s)} emptyCfg

parseFuel3 : String -> Either String $ Config Maybe
parseFuel3 s = pure $ {fuel3 := Just $ limit !(parseNat s)} emptyCfg

parseSeed : String -> Either String $ Config Maybe
parseSeed s = pure $ {seed := Just $ cast !(parseNat s)} emptyCfg

parseMinClust : String -> Either String $ Config Maybe
parseMinClust s = pure $ {minClust := Just !(parseNat s)} emptyCfg

parseOut : String -> Either String $ Config Maybe
parseOut s = pure $ {output := Just s} emptyCfg

parseNodeCfg : String -> Either String $ Config Maybe
parseNodeCfg str with (parsePositive {a = Nat} str)
    _ | (Just x) with (isItSucc x)
      _ | (Yes prf) = Right $ {params := (Just $ MkNodeCfg x)} emptyCfg
      _ | (No contra) = Left "0 is not a positive natural number"
    _ | Nothing = Left "not a natural number"

optDescs : List $ OptDescr $ Config Maybe
optDescs = [ MkOpt ['c'] ["cluster-size"] (ReqArg' parseNodeCfg "<size>") "cluster size in bytes"
       , MkOpt ['1'] ["fuel1"] (ReqArg' parseFuel1 "<fuel1>") "fuel for the Node generator"
       , MkOpt ['2'] ["fuel2"] (ReqArg' parseFuel2 "<fuel2>") "fuel for the NameTree generator"
       , MkOpt ['3'] ["fuel3"] (ReqArg' parseFuel3 "<fuel3>") "fuel for the cmap generator"
       , MkOpt ['s'] ["seed"] (ReqArg' parseSeed "<seed>") "seed"
       , MkOpt ['m'] ["minclust"] (ReqArg' parseMinClust "<minclust>") "minimum amount of data clusters"
       -- , MkOpt ['q'] ["quiet", "no-print"] (NoArg $ {printGen := Just False} emptyCfg) "don't print the generated value"
       , MkOpt ['h'] ["help"] (NoArg $ {help := Just True} emptyCfg) "print usage information"
       , MkOpt ['o'] ["output"] (ReqArg' parseOut "<output>") "output image filename"
       ]


%runElab deriveParam $ map (\n => PI n allIndices [Show]) ["UniqNames", "NameTree", "MaybeNameTree", "HSnocVectNameTree"]

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
    -- let wfs : Maybe (k ** FilesystemB cfg.params k) := runIdentity $ pick @{ConstSeed $ mkStdGen cfg.seed} (genFilesystemB cfg.fuel1 cfg.params)
    -- printLn wfs
    -- let Just (ar@(MkNodeArgs cur tot) ** fs) = wfs
    --     | Nothing => die "failed to generate Node structure"
    -- let Just names = runIdentity $ pick @{ConstSeed $ mkStdGen cfg.seed} (genNameTree cfg.fuel2 cfg.params ar True True fs @{const genBits8} @{const genFilename})
    --     | Nothing => die "failed to generate names"
    -- printLn names
    -- let tcls = maximum 65525 $ maximum cfg.minClust tot
    -- let (Yes nz) = isItSucc tot
    --     | No _ => die "tot is zero"
    -- let Just cvect = runIdentity $ pick @{ConstSeed $ mkStdGen cfg.seed} (genMap tot (tcls `minus` tot))
    --     | Nothing => die "Failed to generate cmap"
    -- printLn cvect
    -- pure ()
    let (Just (image, size)) = runIdentity $ pick @{ConstSeed $ mkStdGen cfg.seed} $ genImage cfg.fuel1 cfg.fuel2 cfg.fuel3 cfg.params cfg.minClust
        | Nothing => die "failed to generate image"
    Right () <- writeBufferToFile cfg.output image size
        | Left err => die "file error: \{show err}"
    pure ()


-- %logging "deptycheck.derive" 5
-- %language ElabReflection
-- %runElab deriveGenPrinter ( Fuel ->
--               (Fuel -> Gen MaybeEmpty Bits8) =>
--               (Fuel -> Gen MaybeEmpty Filename) =>
--               (cfg : NodeCfg) ->
--               (ar : NodeArgs) ->
--               (wb : Bool) ->
--               (fs : Bool) ->
--               (node : Node cfg ar wb fs) ->
--               Gen MaybeEmpty $ NameTree node )
