import Prelude hiding ((<>))
import GHC.SmallStep
import Outputable
import GHC
import GHC.Paths
import System.Environment
import Control.Monad.IO.Class
import DynFlags

import Fact

eval step x = case step x of Nothing -> x
                             Just y -> eval step y

pp :: Outputable a => a -> String
pp = showSDocUnsafe . ppr

ppConf :: Conf -> SDoc
ppConf (heap, e, stack) =
    nest 2 (text "Heap:") $$
    nest 4 (vcat [hang (ppr v <> colon) 2 (ppr e) | (v,e) <- reverse heap ]) $$
    nest 2 (text "Expression:") $$
    nest 4 (ppr e) $$
    nest 2 (text "Stack:") $$
    nest 4 (vcat [ppr s | s <- stack])

main = do
    runGhc (Just libdir) $ do
        -- getSessionDynFlags >>= setSessionDynFlags . flip gopt_set Opt_SuppressUniques
        liftIO $ do
            let e = factExpr 3
            putStrLn $ "Input expression"
            putStrLn $ pp e
            go (initConf e)


go c = case step c of
    Error e -> putStrLn $ "Error: " ++ e
    Done -> putStrLn $ "Done"
    Step c' -> do
        putStrLn "Next:"
        putStrLn $ showSDocUnsafe $ ppConf c'
        go c'
