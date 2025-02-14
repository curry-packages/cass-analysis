--------------------------------------------------------------------------
--- This module contains operations to load and store analysis information
--- persistently in files.
---
--- @author Heiko Hoffmann, Michael Hanus
--- @version January 2025
--------------------------------------------------------------------------

module Analysis.Files where

import Curry.Compiler.Distribution ( installDir )
import Control.Monad       ( when, unless )
import Data.List           ( isPrefixOf, isSuffixOf )

import Data.Time           ( ClockTime )
import FlatCurry.Files
import FlatCurry.Goodies   ( progImports )
import FlatCurry.Types     ( Prog, QName )
import RW.Base             ( ReadWrite )
import System.CurryPath    ( currySubdir, lookupModuleSourceInLoadPath
                           , stripCurrySuffix )
import System.Directory
import System.FilePath

import Analysis.Logging    ( DLevel, debugMessage )
import Analysis.ProgInfo


--- Get the file name in which analysis results are stored
--- (without suffix ".pub" or ".priv")
getAnalysisBaseFile :: String -> String -> IO String
getAnalysisBaseFile moduleName anaName = do
  analysisDirectory <- getAnalysisDirectory
  currentDir        <- getCurrentDirectory >>= return . dropDrive
  let modAnaName = moduleName <.> anaName
  (fileDir,_) <- findModuleSourceInLoadPath moduleName
  if isAbsolute fileDir
   then return (analysisDirectory </> dropDrive fileDir </> modAnaName)
   else return (analysisDirectory </> currentDir </> fileDir </> modAnaName)

--- Get the file name in which public analysis results are stored.
getAnalysisPublicFile :: String -> String -> IO String
getAnalysisPublicFile modname ananame =
  fmap (<.> "pub") $ getAnalysisBaseFile modname ananame

--- Get the file name in which public analysis results are stored.
getAnalysisPrivateFile :: String -> String -> IO String
getAnalysisPrivateFile modname ananame =
  fmap (<.> "priv") $ getAnalysisBaseFile modname ananame

-- Cache directory where analysis info files are stored.
-- If $HOME exists, it is ~/.curry_analysis_cache
getAnalysisDirectory :: IO String
getAnalysisDirectory = do
  homedir <- getHomeDirectory
  hashomedir <- doesDirectoryExist homedir
  let cassStoreDir = if hashomedir then homedir else installDir
  return $ cassStoreDir </> ".curry_analysis_cache" </>
           joinPath (tail (splitDirectories currySubdir))

-- loads analysis results for a list of modules
getInterfaceInfos :: (Read a, ReadWrite a) => DLevel -> String -> [String]
                  -> IO (ProgInfo a)
getInterfaceInfos _  _       [] = return emptyProgInfo
getInterfaceInfos dl anaName (mod:mods) =
  do modInfo  <- loadPublicAnalysis dl anaName mod
     modsInfo <- getInterfaceInfos dl anaName mods
     return (combineProgInfo modInfo modsInfo)

--- Reads the file name in which default analysis values different from
--- standard start values are stored. Typically, such a file contains
--- specific analysis information for external operations.
--- The file must contain a term of the type `[(String,a)]` where
--- the first component of each pair is the name of the operation
--- (it is assumed that this denotes an operation of the current module)
--- and the second component is an analysis value.
loadDefaultAnalysisValues :: Read a => DLevel -> String -> String
                          -> IO [(QName,a)]
loadDefaultAnalysisValues dl anaName moduleName = do
  (_,fileName) <- findModuleSourceInLoadPath moduleName
  let defaultFileName = stripCurrySuffix fileName ++ ".defaults." ++ anaName
  fileExists <- doesFileExist defaultFileName
  if fileExists
    then do debugMessage dl 3 ("Load default values from " ++ defaultFileName)
            defaultValues <- readFile defaultFileName >>= return . read
            return (map (\ (f,a) -> ((moduleName,f),a)) defaultValues)
    else return []

--- Loads the currently stored analysis information for a module.
loadCompleteAnalysis :: (Read a, ReadWrite a) => DLevel -> String -> String
                     -> IO (ProgInfo a)
loadCompleteAnalysis dl ananame mainModule =
  getAnalysisBaseFile mainModule ananame >>= readAnalysisFiles dl

--- Reads analysis result from file for the public entities of a given module.
loadPublicAnalysis :: (Read a, ReadWrite a) => DLevel -> String -> String
                   -> IO (ProgInfo a)
loadPublicAnalysis dl anaName moduleName =
  getAnalysisPublicFile moduleName anaName >>= readAnalysisPublicFile dl

--- Store current import dependencies.
storeImportModuleList :: DLevel -> String -> [String] -> IO ()
storeImportModuleList dl modname modlist = do
  importListFile <- getAnalysisBaseFile modname "IMPORTLIST"
  createDirectoryR dl (dropFileName importListFile)
  writeFile importListFile (show modlist)

--- Gets the file containing import dependencies for a main module
--- (if it exists).
getImportModuleListFile :: String -> IO (Maybe String)
getImportModuleListFile modname = do
  importListFile <- getAnalysisBaseFile modname "IMPORTLIST"
  iflExists <- doesFileExist importListFile
  return $ if iflExists then Just importListFile else Nothing

--- Store an analysis results in a file and create directories if neccesssary.
--- The arguments are the analysis name, the module name and the
--- analysis results for this module.
storeAnalysisResult :: (Show a, ReadWrite a) => DLevel -> String -> String
                    -> ProgInfo a -> IO ()
storeAnalysisResult dl ananame moduleName result = do
  baseFileName <- getAnalysisBaseFile moduleName ananame
  createDirectoryR dl (dropFileName baseFileName)
  debugMessage dl 4 ("Analysis result: " ++ showProgInfo result)
  writeAnalysisFiles dl baseFileName result

-- creates directory (and all needed root-directories) recursively
createDirectoryR :: DLevel -> String -> IO ()
createDirectoryR dl maindir =
  let (drv,dir) = splitDrive maindir
   in createDirectories drv (splitDirectories dir)
 where
  createDirectories _ [] = return ()
  createDirectories dirname (dir:dirs) = do
    let createdDir = dirname </> dir
    dirExists <- doesDirectoryExist createdDir
    unless dirExists $ do
      debugMessage dl 3 ("Creating directory '" ++ createdDir ++ "'...")
      createDirectory createdDir
    createDirectories createdDir dirs

--- Deletes all analysis files for a given analysis name.
deleteAllAnalysisFiles :: String -> IO ()
deleteAllAnalysisFiles ananame = do
  analysisDir <- getAnalysisDirectory
  deleteAllInDir analysisDir
 where
  deleteAllInDir dir = do
    dircont <- getDirectoryContents dir
    mapM_ processDirElem (filter (not . isPrefixOf ".") dircont)
   where
    processDirElem f = do
      let fullname = dir </> f
      when (isAnaFile f) $ do
        putStrLn ("DELETE: " ++ fullname)
        removeFile fullname
      isdir <- doesDirectoryExist fullname
      when isdir $ deleteAllInDir fullname

    isAnaFile f = any hasAnaSuffix [".pub",".priv",".pub.rw",".priv.rw"]
     where
      hasAnaSuffix suf =
        suf `isSuffixOf` f &&
        ('.':ananame) `isSuffixOf` take (length f - length suf) f

--------------------------------------------------------------------------
-- Auxiliaries for dealing with Curry files.

--- Returns a directory name and the actual source file name for a module
--- by looking up the module source in the current load path.
--- If the module is hierarchical, the directory is the top directory
--- of the hierarchy.
--- An error is raised if there is no corresponding source file.
findModuleSourceInLoadPath :: String -> IO (String,String)
findModuleSourceInLoadPath modname =
  lookupModuleSourceInLoadPath modname >>=
  maybe (error $ "Source file for module '"++modname++"' not found!")
        return

--- Get the imports of a module.
getImports :: DLevel -> String -> IO [String]
getImports dl moduleName = do
  debugMessage dl 3 $ "Reading interface of module " ++ moduleName
  readNewestFlatCurryInt moduleName >>= return . progImports

-- Get timestamp of a Curry source module file (together with the module name)
getSourceFileTime :: String -> IO (String,ClockTime)
getSourceFileTime moduleName = do
  (_,fileName) <- findModuleSourceInLoadPath moduleName
  time <- getModificationTime fileName
  return (moduleName,time)

-- Get timestamp of FlatCurry file (together with the module name)
getFlatCurryFileTime :: String -> IO (String,Maybe ClockTime)
getFlatCurryFileTime modname =
  lookupFlatCurryFileInLoadPath modname >>=
  maybe (return (modname, Nothing))
        (\fcyFileName -> do
            ftime <- getModificationTime fcyFileName
            return (modname, Just ftime))

--- Returns name of the FlatCurry file of a module if this file exists
--- and is newer than the source file.
flatCurryFileNewer :: String -> IO (Maybe String)
flatCurryFileNewer modname = do
  (_,sourceFileName) <- findModuleSourceInLoadPath modname
  stime <- getModificationTime sourceFileName
  lookupFlatCurryFileInLoadPath modname >>=
   maybe (return Nothing)
         (\fcyFileName -> do
            itime <- getModificationTime fcyFileName
            return (if itime >= stime then Just fcyFileName else Nothing))

--- Returns the newest FlatCurry program for a module.
--- The source program is parsed if the interface older than the source,
--- otherwise the FlatCurry program is read without parsing
--- (note that this returns only the correct version if the
--- imported modules are already parsed or are not relevant here).
readNewestFlatCurry :: String -> IO Prog
readNewestFlatCurry modname =
  flatCurryFileNewer modname >>=
  maybe (readFlatCurry modname) readFlatCurryFile

--- Returns the newest FlatCurry interface for a module.
--- The source program is parsed if the interface older than the source,
--- otherwise the FlatCurry interface file is read without parsing
--- (note that this returns only the correct version if the
--- imported modules are already parsed or are not relevant here).
readNewestFlatCurryInt :: String -> IO Prog
readNewestFlatCurryInt modname =
  flatCurryFileNewer modname >>=
  maybe (readFlatCurryInt modname) (readFlatCurryFile . flat2intName)

--- Translates FlatCurry file name to corresponding FlatCurry interface
--- file name.
flat2intName :: String -> String
flat2intName fn = reverse ("tnif" ++ drop 3 (reverse fn))
