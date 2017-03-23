module GIFiles where

-- |GUI-independent version of previous code in WxFiles.

import           Compatibility    (utp2try)
import           Files            (FileSpace)
import qualified Files
import qualified System.Directory as SD
import qualified System.FilePath  as SF
import           Utilities        (trim)

-- |GUI dependant data required by functions in this module.
data Args w state = Args {
    aW                   :: w
  , aState               :: state
  , aAppUserDir          :: (state -> FilePath)           -- ^ User's application directory from current state.
  , aCurrentFileSpace    :: (state -> FilePath)           -- ^ Current filespace from current state.
  , aDisplayError        :: (String -> String -> IO ())   -- ^ Display an error with given title and body.
  , aOnAppUserDirError   :: (state -> IO state)           -- ^ What to return on error in 'establishAppUserDirGI'.
  , aFSDirOpenDialog     :: IO (Maybe FilePath)           -- ^ Dialog to select the current working filespace.
  , aFSNameDialog        :: w -> IO String                -- ^ Get name from filespace dialog.
  , aNewFS               :: state -> FileSpace -> state   -- ^ Create a new filespace from current state, name and cwd.
  , aReadFSPFileNewState :: state -> [FileSpace] -> state -- ^ Determine new state in 'readFSPs_GI'.
  , aWriteFSPFileFSPs    :: state -> [FileSpace]
  }

startupFileHandling_GI :: Args w state -> IO (Args w state)
startupFileHandling_GI args = do
  args'  <- determineAppData_GI args
  args'' <- accessFrameworkData_GI args'
  return args''

-- |Does the directory exist ? If not, initialise it. Does the set-up file exist
-- ? If not, initialise it. Read the set-up file to get the current and previous
-- filesspaces, initialising the current, if corrupted.
determineAppData_GI :: Args w state -> IO (Args w state)
determineAppData_GI args = do
  args'  <- establishAppUserDir_GI args
  args'' <- determineFSPs_GI       args'
  return args''

-- |Does it exist ? if not, initialise it. Does the framework file exist ? If
-- not, initialise it. Read the framework file, initialising if corrupt. Does
-- the current proof file exist ? If not, initialise it. Read the current proof
-- file, initialising if corrupted.
accessFrameworkData_GI :: Args w state -> IO (Args w state)
accessFrameworkData_GI args = do
  let cwdpath = aCurrentFileSpace args $ aState args
  mres1 <- utp2try $ SD.createDirectoryIfMissing True cwdpath
  -- explainError mres1
  mres3 <- utp2try $ SD.setCurrentDirectory cwdpath
  -- explainError mres3
  -- xxx <- getCurrentDirectory
  --toConsole $ "\n\n***CURR DIR NOW = "++xxx
  return args

establishAppUserDir_GI :: Args w state -> IO (Args w state)
establishAppUserDir_GI args = do
  let dirpath = aAppUserDir args $ aState args
  present <- SD.doesDirectoryExist dirpath
  if   present
  then return args
  else do
    res <- utp2try $ SD.createDirectory dirpath
    case res of
      Right _       -> return  args
      Left  ioError -> do
        aDisplayError args "Cannot create directory" $ msg ioError dirpath
        state' <- aOnAppUserDirError args $ aState args
        return $ args { aState = state' }
  where
    msg err path = unlines [
        "Cannot create application user data directory"
      , " "++path
      , " "++show err
      , "- consult an os-wizard for assistance."
      , ""
      , "For now, you will be prompted for your working filespace"
      , "every time this application is launched"
      ]

determineFSPs_GI :: Args w state -> IO (Args w state)
determineFSPs_GI args = do
  let  audPath = aAppUserDir args $ aState args
  if   null audPath
  then userCreateFS_GI   args
  else fileLookupFSPs_GI args

userCreateFS_GI :: Args w state -> IO (Args w state)
userCreateFS_GI args = do
  mcwd <- aFSDirOpenDialog args
  case mcwd of
    Nothing  -> do
      aDisplayError args "Don't know the current filespace" ""
      error "No FileSpace defined"
    Just cwd -> do
      name <- aFSNameDialog args $ aW args
      let newFS = aNewFS args (aState args) (name, cwd)
      return $ args { aState = newFS }

fileLookupFSPs_GI :: Args w state -> IO (Args w state)
fileLookupFSPs_GI args = do
  let cfgpath = concat [
          aAppUserDir args $ aState args
        , [SF.pathSeparator]
        , Files.acalai
        , Files.cumraiocht
        ]
  present <- SD.doesFileExist cfgpath
  return args
  if   present
  then readFSPFile_GI args cfgpath
  else do
    args' <- userCreateFS_GI args
    writeFSPFile_GI cfgpath args'
    return args'

readFSPFile_GI :: Args w state -> FilePath -> IO (Args w state)
readFSPFile_GI args path = do
  txt <- readFile path
  let fsps = filter validFS $ map fsParse $ lines txt
  if   null fsps
  then userCreateFS_GI args
  else do
    let state = aReadFSPFileNewState args (aState args) fsps
    return args { aState = state }

writeFSPFile_GI :: FilePath -> Args w state -> IO ()
writeFSPFile_GI path args = do
  let fsps = aWriteFSPFileFSPs args $ aState args
  writeFile path (unlines (map showFSP fsps))
  where showFSP (name, path) = name ++ namePathSep:path

fsParse txt = (name, path)
  where (name, rest) = break (== namePathSep) txt
        path = if null rest then "" else tail rest

validFS (_, path) = not $ null $ trim $ path

namePathSep = ';'
