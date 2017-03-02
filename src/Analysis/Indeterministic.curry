------------------------------------------------------------------------------
--- Indeterminism analysis:
--- check whether functions are indeterministic, i.e., might deliver
--- different results for different runs of a program.
--- This could be the case if there are explicit or implicit calls
--- to `SetFunctions.select` or to a committed choice.
---
--- @author Michael Hanus
--- @version April 2013
------------------------------------------------------------------------------

module Analysis.Indeterministic(indetAnalysis,showIndet) where

import Analysis.Types
import FlatCurry.Types

------------------------------------------------------------------------------
--- The indeterminism analysis is a global function dependency analysis.
--- It assigns to a function a flag which is True if this function
--- might be indeterministic (i.e., calls directly or indirectly
--- a select or committed choice operation).

indetAnalysis :: Analysis Bool
indetAnalysis = dependencyFuncAnalysis "Indeterministic" False indetFunc

--- An operation is indeterministic if it calls a select or committed choice
--- or depends on some indeterministic operation.
indetFunc  :: FuncDecl -> [(QName,Bool)] -> Bool
indetFunc func calledFuncs =
  hasIndetRules func || any snd calledFuncs

-- Show right-linearity information as a string.
showIndet :: AOutFormat -> Bool -> String
showIndet AText True  = "impure (indeterministic) operation"
showIndet ANote True  = "indeterministic"
showIndet AText False = "referentially transparent operation"
showIndet ANote False = "" 

------------------------------------------------------------------------------
-- The right-linearity analysis can also be applied to individual functions.
-- It returns True for a function if it is defined by right-linear rules.

hasIndetRules :: FuncDecl -> Bool
hasIndetRules (Func _ _ _ _ (Rule _ e))   = choiceInExpr e
hasIndetRules (Func _ _ _ _ (External _)) = False

-- check an expression for occurrences of select, committed choice, or send:
choiceInExpr :: Expr -> Bool
choiceInExpr (Var _) = False
choiceInExpr (Lit _) = False
choiceInExpr (Comb _ f es) = f `elem` indetFuns || any choiceInExpr es
choiceInExpr (Free _ e) = choiceInExpr e
choiceInExpr (Let bs e) = any choiceInExpr (map snd bs) || choiceInExpr e
choiceInExpr (Or e1 e2) = choiceInExpr e1 || choiceInExpr e2
choiceInExpr (Case _  e bs) = choiceInExpr e || any choiceInBranch bs
                where choiceInBranch (Branch _ be) = choiceInExpr be
choiceInExpr (Typed e _) = choiceInExpr e

indetFuns :: [QName]
indetFuns = [("Prelude","commit"),
             ("Ports","send"),("Ports","doSend"),
             ("SetFunctions","select")]

-- end of Indeterministic
