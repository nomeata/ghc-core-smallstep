import GHC.SmallStep
import GHC.SmallStep.Tests
import Outputable
import StaticFlags
import GHC
import System.Environment
import Control.Monad.IO.Class
import DynFlags

eval step x = case step x of Nothing -> x
                             Just y -> eval step y

pp :: Outputable a => a -> String
pp = showSDocUnsafe . ppr

main = do
    [libdir] <- getArgs
    runGhc (Just libdir) $ do
        getSessionDynFlags >>= setSessionDynFlags . flip gopt_set Opt_SuppressUniques
        liftIO $ do
            let e = factExpr 3
            putStrLn $ "Input expression"
            putStrLn $ pp e
            go (initConf e)


go c = case step c of
    Nothing -> putStrLn $ "Done"
    Just c' -> do
        putStrLn "Next:"
        putStrLn $ pp $ c'
        go c'
