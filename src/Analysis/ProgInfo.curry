-----------------------------------------------------------------------
--- This module defines a datatype to represent the analysis information.
---
--- @author Heiko Hoffmann, Michael Hanus
--- @version January 2015
-----------------------------------------------------------------------

module Analysis.ProgInfo
  ( ProgInfo, emptyProgInfo, lookupProgInfo, combineProgInfo
  , lists2ProgInfo, publicListFromProgInfo, progInfo2Lists, progInfo2XML
  , mapProgInfo, publicProgInfo
  , showProgInfo
  , readAnalysisFiles, readAnalysisPublicFile, writeAnalysisFiles
  ) where

import System.Directory     (removeFile)
import qualified Data.Map as Map
import System.FilePath      ((<.>))
import FlatCurry.Types
import XML

import Analysis.Logging (debugMessage)

--- Type to represent analysis information.
--- The first component are public declarations, the second the private ones.
data ProgInfo a = ProgInfo (Map.Map QName a) (Map.Map QName a)
  deriving Eq

--- The empty program information.
emptyProgInfo:: ProgInfo a
emptyProgInfo = ProgInfo Map.empty Map.empty

--- Gets the information about an entity.
lookupProgInfo:: QName -> ProgInfo a -> Maybe a
lookupProgInfo key (ProgInfo map1 map2) =
 case Map.lookup key map1 of
  Just x  -> Just x
  Nothing ->  Map.lookup key map2

--- Combines two analysis informations.
combineProgInfo :: ProgInfo a -> ProgInfo a -> ProgInfo a
combineProgInfo (ProgInfo x1 x2) (ProgInfo y1 y2) =
  ProgInfo (Map.union x1 y1) (Map.union x2 y2)

--- Converts a public and a private analysis list into a program info.
lists2ProgInfo :: ([(QName,a)],[(QName,a)]) -> ProgInfo a
lists2ProgInfo (xs,ys) = ProgInfo (Map.fromList xs) (Map.fromList ys)

--- Returns the infos of public operations as a list.
publicListFromProgInfo:: ProgInfo a -> [(QName,a)]
publicListFromProgInfo (ProgInfo fm1 _) = Map.toList fm1

--- Transforms a program information into a pair of lists
--- containing the information about public and private entities.
progInfo2Lists :: ProgInfo a -> ([(QName,a)],[(QName,a)])
progInfo2Lists (ProgInfo map1 map2)= (Map.toList map1,Map.toList map2)

--- Transforms analysis information into XML format.
progInfo2XML :: ProgInfo String -> ([XmlExp],[XmlExp])
progInfo2XML (ProgInfo map1 map2) =
  (Map.foldrWithKey entry2xml [] map1, Map.foldrWithKey entry2xml [] map2)
 where
  entry2xml (mname,name) value xmlList =
    (xml "operation" [xml "module" [xtxt mname],
                      xml "name"   [xtxt name],
                      xml "result" [xtxt value]]) : xmlList

mapProgInfo:: (a->b) -> ProgInfo a -> ProgInfo b
mapProgInfo func (ProgInfo map1 map2) =
  ProgInfo (Map.mapWithKey (\_ b->func b) map1)
           (Map.mapWithKey (\_ b->func b) map2)

--- Transforms a program information into a program information
--- about interface entities only.
publicProgInfo :: ProgInfo a -> ProgInfo a
publicProgInfo (ProgInfo pub _) = ProgInfo pub Map.empty

--- Show a ProgInfo as a string (used for debugging only).
showProgInfo :: Show a => ProgInfo a -> String
showProgInfo (ProgInfo fm1 fm2) =
  "Public: "++show fm1++"\nPrivate: "++show fm2

--- Writes a ProgInfo into a file.
writeAnalysisFiles :: Show a => String -> ProgInfo a -> IO ()
writeAnalysisFiles basefname (ProgInfo pub priv) = do
  debugMessage 3 $ "Writing analysis files '"++basefname++"'..."
  writeFile (basefname <.> "priv") (show priv)
  writeFile (basefname <.> "pub")  (show pub)

--- Reads a ProgInfo from the analysis files where the base file name is given.
readAnalysisFiles :: Read a => String -> IO (ProgInfo a)
readAnalysisFiles basefname = do
  debugMessage 3 $ "Reading analysis files '"++basefname++"'..."
  let pubcontfile  = basefname <.> "pub"
      privcontfile = basefname <.> "priv"
  pubcont  <- readFile pubcontfile
  privcont <- readFile privcontfile
  let pinfo = ProgInfo (read pubcont) (read privcont)
  catch (return $!! pinfo)
        (\err -> do
           putStrLn ("Buggy analysis files detected and removed:\n"++
                     basefname)
           mapIO_ removeFile [pubcontfile,privcontfile]
           putStrLn "Please try to re-run the analysis!"
           ioError err)

--- Reads the public ProgInfo from the public analysis file.
readAnalysisPublicFile :: Read a => String -> IO (ProgInfo a)
readAnalysisPublicFile fname = do
  debugMessage 3 $ "Reading public analysis file '"++fname++"'..."
  fcont <- readFile fname
  let pinfo = ProgInfo (read fcont) Map.empty
  catch (return $!! pinfo)
        (\err -> do
           putStrLn ("Buggy analysis files detected and removed:\n"++fname)
           removeFile fname
           putStrLn "Please try to re-run the analysis!"
           ioError err)

-----------------------------------------------------------------------
