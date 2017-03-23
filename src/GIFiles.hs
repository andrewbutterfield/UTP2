module GIFiles where

-- |GUI-independent version of previous code in WxFiles.

import           Compatibility    (utp2try)
import           System.Directory (createDirectory, createDirectoryIfMissing,
                                   doesDirectoryExist, setCurrentDirectory)

data Args w state = Args {
    aW                 :: w
  , aState             :: state
  , aAppUserDir        :: (state -> FilePath)   -- ^ The application user's directory.
  , aCurrentFileSpace  :: (state -> FilePath)
  , aDisplayError      :: (String -> IO ())     -- ^ Display an error with given string.
  , aOnAppUserDirError :: (state -> IO state)   -- ^ Run on error.
  }

startupFileHandlingGI :: Args w state -> IO (Args w state)
startupFileHandlingGI = return
  -- state'  <- determineAppDataGI    a state appUserDir
  -- state'' <- accessFrameworkDataGI a state currentFileSpace
  -- return state''

-- |Does the directory exist ? If not, initialise it. Does the set-up file exist
-- ? If not, initialise it. Read the set-up file to get the current and previous
-- filesspaces, initialising the current, if corrupted.
-- determineAppDataGI :: a -> b -> (b -> FilePath) -> b
-- determineAppDataGI a state appUserDir = do
--   state'  <- establishAppUserDirGI a state
--   state'' <- determineFSPsGI       a state appUserDir
  -- return state''

-- |Does it exist ? if not, initialise it. Does the framework file exist ? If
-- not, initialise it. Read the framework file, initialising if corrupt. Does
-- the current proof file exist ? If not, initialise it. Read the current proof
-- file, initialising if corrupted.
-- accessFrameworkDataGI :: a -> b -> (b -> [FilePath]) -> b
-- accessFrameworkDataGI a b currentFileSpace = do
--   let cwdpath = snd $ currentFileSpace b
--   mres1 <- utp2try $ createDirectoryIfMissing True cwdpath
--   -- explainError mres1
--   mres3 <- utp2try $ setCurrentDirectory cwdpath
--   -- explainError mres3
--   -- xxx <- getCurrentDirectory
--   --toConsole $ "\n\n***CURR DIR NOW = "++xxx
--   return b

establishAppUserDirGI ::
     String            -- ^ The application user's directory.
  -> (String -> IO ()) -- ^ Display an error with given string.
  -> (a -> IO a)       -- ^ What to return on error.
  -> a                 -- ^ Input value, on success this is returned.
  -> IO a              -- ^ Return the last argument.
establishAppUserDirGI dirpath displayError onError val = do
  present <- doesDirectoryExist dirpath
  if   present
  then return val
  else do
    res <- utp2try $ createDirectory dirpath
    case res of
      Right _       -> return val
      Left  ioError -> do
        displayError $ msg ioError dirpath
        onError val
  where
    msg err path = unlines [
        "Cannot create application user data directory"
      , " "++path
      , " "++show err
      , "- consult a os-wizard for assistance."
      , ""
      , "For now, you will be prompted for your working filespace"
      , "every time this application is launched"
      ]

determineFSPsGI :: a -> b -> (b -> FilePath) -> b
determineFSPsGI a state appUserDir = do
  let  audPath = appUserDir state
  if   null audPath
  then userCreateFS_GI  a state
  else fileLookupFSPsGI a state

userCreateFS_GI a state = state

fileLookupFSPsGI a state = state
