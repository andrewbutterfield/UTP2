module GIFiles where

-- |GUI-independent version of previous code in WxFiles.

import           Compatibility
import           System.Directory (createDirectory, doesDirectoryExist)

-- |GUI independent version of 'establishAppUserDir'.
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
