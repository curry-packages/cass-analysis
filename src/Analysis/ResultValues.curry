-----------------------------------------------------------------------------
--- An analysis to approximate the result values of operations
--- in a Curry program.
--- This analysis approximates the outermost constructors of the results.
--- Thus, `Cons [c1,...,ck]` means that any result returned by an
--- operation is rooted by some of the constructors `c1,...,ck`.
--- The abstract value `Any` means that there is a no precise information
--- about the outermost constructors.
---
--- @author Michael Hanus
--- @version June 2023
-----------------------------------------------------------------------------

module Analysis.ResultValues
  (AType(..), showAType, resultValueAnalysis)
 where

import Data.List         hiding (union, intersect)

import FlatCurry.Types

import Analysis.Types
import Analysis.ProgInfo

------------------------------------------------------------------------------
-- Our abstract (non-standard) type domain.
-- `Any` represents any expression,
-- `AnyC` represents any value (i.e., constructor-rooted term),
-- `Cons cs` a value rooted by some of the constructor `cs`, and
data AType = Cons [QName] | Any
 deriving (Eq, Ord, Show, Read)

-- A literal `l` is represented as a constructor `("",l)`.
lit2cons :: Literal -> QName
lit2cons l = ("", showLit l)
 where
  showLit (Intc i) = show i
  showLit (Floatc x) = show x
  showLit (Charc c) = show c

--- Abstract representation of no possible value.
emptyAType :: AType
emptyAType = Cons []

--- Least upper bound of abstract values.
lubAType :: AType -> AType -> AType
lubAType Any      _        = Any
lubAType (Cons _) Any      = Any
lubAType (Cons c) (Cons d) = Cons (union c d)

--- Join two abstract values.
--- The result is `emptyAType` if they are not compatible.
joinAType :: AType -> AType -> AType
joinAType Any      av       = av
joinAType (Cons c) Any      = Cons c
joinAType (Cons c) (Cons d) = Cons (intersect c d)
-- replace previous rule by following rule in order to use singleton sets:
--joinAType (Cons c) (Cons d) = if c==d then Cons c else Cons []

-- Shows an abstract value.
showAType :: AOutFormat -> AType -> String
showAType _ Any       = "any"
showAType _ (Cons cs) = "{" ++ intercalate "," (map snd cs) ++ "}"

------------------------------------------------------------------------------
--- An abstract environments used in the analysis of a function associates
--- to each variable (index) an abstract type.
type AEnv = [(Int,AType)]

--- Extend an abstract environment with variables of any type:
extendEnv :: AEnv -> [Int] -> AEnv
extendEnv env vars = zip vars (repeat Any) ++ env

------------------------------------------------------------------------------

--- Required value analysis.
resultValueAnalysis :: Analysis AType
resultValueAnalysis =
  dependencyFuncAnalysis "ResultValues" emptyAType analyseResultValue

analyseResultValue :: FuncDecl -> [(QName,AType)] -> AType
analyseResultValue (Func (m,f) _ _ _ rule) calledfuncs
 | m==prelude = maybe (anaresult rule) id (lookup f preludeFuncs)
 | otherwise  = anaresult rule
 where
  -- add special results for prelude functions here:
  preludeFuncs = [ ("failed", emptyAType)
                 , ("error", emptyAType)
                 ]

  anaresult (External _)    = Any
  anaresult (Rule args rhs) = anaExpr (extendEnv [] args) rhs

  anaExpr args exp = case exp of
    Var v         -> maybe Any id (lookup v args)
    Lit l         -> Cons [lit2cons l]
    Comb ct qf es -> if ct == FuncCall
                       then if qf == (prelude,"?") && length es == 2
                              then anaExpr args (Or (es!!0) (es!!1))
                              else maybe Any id (lookup qf calledfuncs)
                       else Cons [qf]
    Let bs e      -> anaExpr (map (\ (v,ve) -> (v, anaExpr args ve)) bs ++ args)
                             e
    Free vs e     -> anaExpr (extendEnv args vs) e
    Or e1 e2      -> lubAType (anaExpr args e1) (anaExpr args e2)
    Case _ _ bs   -> foldr lubAType emptyAType
                           (map (\ (Branch _ e) -> anaExpr args e) bs)
    Typed e _     -> anaExpr args e

-- Name of the standard prelude:
prelude :: String
prelude = "Prelude"

------------------------------------------------------------------------------
-- Auxiliaries:

-- Union on sorted lists:
union :: Ord a => [a] -> [a] -> [a]
union []       ys     = ys
union xs@(_:_) []     = xs
union (x:xs)   (y:ys) | x==y      = x : union xs ys
                      | x<y       = x : union xs (y:ys)
                      | otherwise = y : union (x:xs) ys

-- Intersection on sorted lists:
intersect :: Ord a => [a] -> [a] -> [a]
intersect []     _      = []
intersect (_:_)  []     = []
intersect (x:xs) (y:ys) | x==y      = x : intersect xs ys
                        | x<y       = intersect xs (y:ys)
                        | otherwise = intersect (x:xs) ys

------------------------------------------------------------------------------
