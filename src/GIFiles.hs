module GIFiles where

-- |GUI-independent version of previous code in WxFiles.

import           Compatibility    (utp2try)
import           Files            (FileSpace)
import qualified Files
import qualified System.Directory as SD
import qualified System.FilePath  as SF
import           Utilities        (trim)
import           WxState          (FileState (..), emptyFS, newFS)

-- |GUI dependent data required by functions in this module.
data Args w = Args {
    aW                   :: w                           -- ^ Additional argument required by Wx.
  , aFstate              :: FileState                   -- ^ The current filestate.
  , aDisplayError        :: (String -> String -> IO ()) -- ^ Display an error with given title and body.
  , aFSDirOpenDialog     :: IO (Maybe FilePath)         -- ^ Dialog to select the current workspace if none.
  , aFSNameDialog        :: w -> IO String              -- ^ Get name from filespace dialog.
  }

saoithinExeName = "UTP2"

systemFilePaths :: IO (String, FileState)
systemFilePaths = do
  user    <- getUsername
  appuser <- dirget (SD.getAppUserDataDirectory saoithinExeName) "App User Data" ""
  return (user, emptyFS { appUserDir=appuser })

getUsername :: IO String
getUsername = do
  attempt <- utp2try SD.getHomeDirectory
  case attempt of
    Left ioerror -> do
      putStrLn $ "Cannot get username: " ++ show ioerror
      return "_anonymous_"
    Right uhome  -> return $ extractUsername "" $ reverse uhome

extractUsername uname "" = uname
extractUsername uname (c:cs)
 | c == '\\'  =  uname
 | c == '/'   =  uname
 | otherwise  =  extractUsername (c:uname) cs

dirget get descr def = do
  attempt <- utp2try $ get
  case attempt of
    Left ioerror -> do
      putStrLn $ concat [
          "Cannot get "
        , descr
        , " Directory : "
        , show ioerror
        ]
      return def
    Right thing  -> return thing

startupFileHandling_GI :: Args w -> IO (Args w)
startupFileHandling_GI args = do
  args'  <- determineAppData_GI args
  args'' <- accessFrameworkData_GI args'
  return args''

-- |Does the directory exist ? If not, initialise it. Does the set-up file exist
-- ? If not, initialise it. Read the set-up file to get the current and previous
-- filesspaces, initialising the current, if corrupted.
determineAppData_GI :: Args w -> IO (Args w)
determineAppData_GI args = do
  args'  <- establishAppUserDir_GI args
  args'' <- determineFSPs_GI       args'
  return args''

-- |Does it exist ? if not, initialise it. Does the framework file exist ? If
-- not, initialise it. Read the framework file, initialising if corrupt. Does
-- the current proof file exist ? If not, initialise it. Read the current proof
-- file, initialising if corrupted.
accessFrameworkData_GI :: Args w -> IO (Args w)
accessFrameworkData_GI args = do
  let cwdpath = snd $ currentFileSpace $ aFstate args
  mres1 <- utp2try $ SD.createDirectoryIfMissing True cwdpath
  -- explainError mres1
  mres3 <- utp2try $ SD.setCurrentDirectory cwdpath
  -- explainError mres3
  -- xxx <- getCurrentDirectory
  --toConsole $ "\n\n***CURR DIR NOW = "++xxx
  return args

establishAppUserDir_GI :: Args w -> IO (Args w)
establishAppUserDir_GI args = do
  let dirpath = appUserDir $ aFstate args
  present <- SD.doesDirectoryExist dirpath
  if   present
  then return args
  else do
    res <- utp2try $ SD.createDirectory dirpath
    case res of
      Right _       -> return args
      Left  ioError -> do
        aDisplayError args "Cannot create directory" $ msg ioError dirpath
        let fstate = (aFstate args) { appUserDir = "" }
        return $ args { aFstate = fstate }
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

determineFSPs_GI :: Args w -> IO (Args w)
determineFSPs_GI args = do
  let  audPath = appUserDir $ aFstate args
  if   null audPath
  then userCreateFS_GI   args
  else fileLookupFSPs_GI args

userCreateFS_GI :: Args w -> IO (Args w)
userCreateFS_GI args = do
  mcwd <- aFSDirOpenDialog args
  case mcwd of
    Nothing  -> do
      aDisplayError args "Don't know the current filespace" ""
      error "No FileSpace defined"
    Just cwd -> do
      name <- aFSNameDialog args $ aW args
      return $ args { aFstate = newFS (aFstate args) (name, cwd) }

fileLookupFSPs_GI :: Args w -> IO (Args w)
fileLookupFSPs_GI args = do
  let cfgpath = concat [
          appUserDir $ aFstate args
        , [SF.pathSeparator]
        , Files.acalai
        , Files.cumraiocht
        ]
  present <- SD.doesFileExist cfgpath
  if   present
  then readFSPFile_GI args cfgpath
  else do
    args' <- userCreateFS_GI args
    writeFSPFile_GI cfgpath args'
    return args'

readFSPFile_GI :: Args w -> FilePath -> IO (Args w)
readFSPFile_GI args path = do
  txt <- readFile path
  let fsps = filter validFS $ map fsParse $ lines txt
  if   null fsps
  then userCreateFS_GI args
  else do
    let state = (aFstate args) {
            currentFileSpace = head fsps
          , previousFileSpaces = tail fsps
          }
    return args { aFstate = state }

writeFSPFile_GI :: FilePath -> Args w -> IO ()
writeFSPFile_GI path args = do
  let fstate = aFstate args
      fsps = (currentFileSpace fstate):(previousFileSpaces fstate)
  writeFile path $ unlines $ map showFSP fsps
  where showFSP (name, path) = name ++ namePathSep:path

fsParse txt = (name, path)
  where (name, rest) = break (== namePathSep) txt
        path = if null rest then "" else tail rest

validFS (_, path) = not $ null $ trim $ path

namePathSep = ';'
