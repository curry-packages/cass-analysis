------------------------------------------------------------------------
--- An analysis which returns information whether a module is unsafe, i.e.,
--- it imports directly or indirectly the module `System.IO.Unsafe` or
--- related unsafe modules.
---
--- @author Michael Hanus
--- @version February 2025
------------------------------------------------------------------------

module Analysis.UnsafeModule ( showUnsafe, unsafeModuleAnalysis )
 where

import Data.List         ( isInfixOf, nub )

import Analysis.Types
import FlatCurry.Goodies ( progImports, progName )
import FlatCurry.Types

------------------------------------------------------------------------
--- This analysis associates to a module the list of the names of all
--- modules which directly imports the module `Unsafe`.
--- Such modules might hide dangerous operations in
--- purely functional operations.
--- Thus, a module is safe if the analysis result is the empty list.

unsafeModuleAnalysis :: Analysis [String]
unsafeModuleAnalysis = dependencyModuleAnalysis "UnsafeModule" importsUnsafe

-- Show the information about unsafe modules as a string.
showUnsafe :: AOutFormat -> [String] -> String
showUnsafe _     []         = "safe"
showUnsafe ANote (_:_)      = "unsafe"
showUnsafe AText [mod]      = "unsafe (due to module " ++ mod ++ ")"
showUnsafe AText ms@(_:_:_) = "unsafe (due to modules " ++ unwords ms ++ ")"

-- Is a module or one of its imports an unsafe module like `System.IO.Unsafe`
-- or any other unsafe module?
-- TODO: to be real safe, one also has to check external operations!
importsUnsafe :: Prog -> [(String,[String])] -> [String]
importsUnsafe prog impinfos =
  let unsafemods = (if any ("Unsafe" `isInfixOf`)
                           (progName prog : progImports prog)
                      then [progName prog]
                      else []) ++
                   concatMap snd impinfos
  in nub unsafemods

-----------------------------------------------------------------------
