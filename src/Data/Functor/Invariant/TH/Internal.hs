{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE TemplateHaskellQuotes #-}
#endif

{-|
Module:      Data.Functor.Invariant.TH.Internal
Copyright:   (C) 2012-2017 Nicolas Frisby, (C) 2015-2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Portability: Template Haskell

Template Haskell-related utilities.
-}
module Data.Functor.Invariant.TH.Internal where

import           Data.Foldable (foldr')
import           Data.Functor.Invariant () -- To import the instances
import qualified Data.List as List
import qualified Data.Map as Map (singleton)
import           Data.Map (Map)
import           Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)

import           Language.Haskell.TH.Datatype
import           Language.Haskell.TH.Lib
import           Language.Haskell.TH.Syntax

#if __GLASGOW_HASKELL__ >= 800
import           Data.Coerce (coerce)
import           Data.Functor.Invariant (Invariant(..), Invariant2(..))
#else
# ifndef CURRENT_PACKAGE_KEY
import           Data.Version (showVersion)
import           Paths_invariant (version)
# endif
#endif

-------------------------------------------------------------------------------
-- Expanding type synonyms
-------------------------------------------------------------------------------

applySubstitutionKind :: Map Name Kind -> Type -> Type
#if MIN_VERSION_template_haskell(2,8,0)
applySubstitutionKind = applySubstitution
#else
applySubstitutionKind _ t = t
#endif

substNameWithKind :: Name -> Kind -> Type -> Type
substNameWithKind n k = applySubstitutionKind (Map.singleton n k)

substNamesWithKindStar :: [Name] -> Type -> Type
substNamesWithKindStar ns t = foldr' (flip substNameWithKind starK) t ns

-------------------------------------------------------------------------------
-- Class-specific constants
-------------------------------------------------------------------------------

-- | A representation of which @Invariant@ is being used.
data InvariantClass = Invariant | Invariant2
  deriving (Eq, Ord)

instance Enum InvariantClass where
    fromEnum Invariant  = 1
    fromEnum Invariant2 = 2

    toEnum 1 = Invariant
    toEnum 2 = Invariant2
    toEnum i = error $ "No Invariant class for number " ++ show i

invmapConstName :: InvariantClass -> Name
invmapConstName Invariant  = invmapConstValName
invmapConstName Invariant2 = invmap2ConstValName

invariantClassName :: InvariantClass -> Name
invariantClassName Invariant  = invariantTypeName
invariantClassName Invariant2 = invariant2TypeName

invmapName :: InvariantClass -> Name
invmapName Invariant  = invmapValName
invmapName Invariant2 = invmap2ValName

-- | A type-restricted version of 'const'. This constrains the map functions
-- that are autogenerated by Template Haskell to be the correct type, even
-- if they aren't actually used in an invmap(2) expression. This is useful
-- in makeInvmap(2), since a map function might have its type inferred as
-- @a@ instead of @a -> b@ (which is clearly wrong).
invmapConst :: f b -> (a -> b) -> (b -> a) -> f a -> f b
invmapConst = const . const . const
{-# INLINE invmapConst #-}

invmap2Const :: f c d
             -> (a -> c) -> (c -> a)
             -> (b -> d) -> (d -> b)
             -> f a b -> f c d
invmap2Const = const . const . const . const . const
{-# INLINE invmap2Const #-}

-------------------------------------------------------------------------------
-- StarKindStatus
-------------------------------------------------------------------------------

-- | Whether a type is not of kind *, is of kind *, or is a kind variable.
data StarKindStatus = NotKindStar
                    | KindStar
                    | IsKindVar Name
  deriving Eq

-- | Does a Type have kind * or k (for some kind variable k)?
canRealizeKindStar :: Type -> StarKindStatus
canRealizeKindStar t
  | hasKindStar t = KindStar
  | otherwise = case t of
#if MIN_VERSION_template_haskell(2,8,0)
                     SigT _ (VarT k) -> IsKindVar k
#endif
                     _               -> NotKindStar

-- | Returns 'Just' the kind variable 'Name' of a 'StarKindStatus' if it exists.
-- Otherwise, returns 'Nothing'.
starKindStatusToName :: StarKindStatus -> Maybe Name
starKindStatusToName (IsKindVar n) = Just n
starKindStatusToName _             = Nothing

-- | Concat together all of the StarKindStatuses that are IsKindVar and extract
-- the kind variables' Names out.
catKindVarNames :: [StarKindStatus] -> [Name]
catKindVarNames = mapMaybe starKindStatusToName

-------------------------------------------------------------------------------
-- Assorted utilities
-------------------------------------------------------------------------------

-- | Returns True if a Type has kind *.
hasKindStar :: Type -> Bool
hasKindStar VarT{}         = True
#if MIN_VERSION_template_haskell(2,8,0)
hasKindStar (SigT _ StarT) = True
#else
hasKindStar (SigT _ StarK) = True
#endif
hasKindStar _              = False

-- Returns True is a kind is equal to *, or if it is a kind variable.
isStarOrVar :: Kind -> Bool
#if MIN_VERSION_template_haskell(2,8,0)
isStarOrVar StarT  = True
isStarOrVar VarT{} = True
#else
isStarOrVar StarK  = True
#endif
isStarOrVar _      = False

-- | @hasKindVarChain n kind@ Checks if @kind@ is of the form
-- k_0 -> k_1 -> ... -> k_(n-1), where k0, k1, ..., and k_(n-1) can be * or
-- kind variables.
hasKindVarChain :: Int -> Type -> Maybe [Name]
hasKindVarChain kindArrows t =
  let uk = uncurryKind (tyKind t)
  in if (length uk - 1 == kindArrows) && all isStarOrVar uk
        then Just (freeVariables uk)
        else Nothing

-- | If a Type is a SigT, returns its kind signature. Otherwise, return *.
tyKind :: Type -> Kind
tyKind (SigT _ k) = k
tyKind _          = starK

-- | A mapping of type variable Names to their map function Names. For example, in a
-- Invariant declaration, a TyVarMap might look like:
--
--   (a ~> (covA, contraA), b ~> (covB, contraB))
--
-- where a and b are the last two type variables of the datatype, and covA and covB
-- are the two map functions for a and b in covariant positions, and contraA and
-- contraB are the two map functions for a and b in contravariant positions.
type TyVarMap = Map Name (Name, Name)

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

-- Like 'lookup', but for lists of triples.
lookup2 :: Eq a => a -> [(a, b, c)] -> Maybe (b, c)
lookup2 _ [] = Nothing
lookup2 key ((x,y,z):xyzs)
    | key == x  = Just (y, z)
    | otherwise = lookup2 key xyzs

-- | Generate a list of fresh names with a common prefix, and numbered suffixes.
newNameList :: String -> Int -> Q [Name]
newNameList prefix n = mapM (newName . (prefix ++) . show) [1..n]

createKindChain :: Int -> Kind
createKindChain = go starK
  where
    go :: Kind -> Int -> Kind
    go k 0 = k
    go k n = n `seq` go (arrowKCompat starK k) (n - 1)

-- | Applies a typeclass constraint to a type.
applyClass :: Name -> Name -> Pred
#if MIN_VERSION_template_haskell(2,10,0)
applyClass con t = AppT (ConT con) (VarT t)
#else
applyClass con t = ClassP con [VarT t]
#endif

-- | Checks to see if the last types in a data family instance can be safely eta-
-- reduced (i.e., dropped), given the other types. This checks for three conditions:
--
-- (1) All of the dropped types are type variables
-- (2) All of the dropped types are distinct
-- (3) None of the remaining types mention any of the dropped types
canEtaReduce :: [Type] -> [Type] -> Bool
canEtaReduce remaining dropped =
       all isTyVar dropped
    && allDistinct droppedNames -- Make sure not to pass something of type [Type], since Type
                                -- didn't have an Ord instance until template-haskell-2.10.0.0
    && not (any (`mentionsName` droppedNames) remaining)
  where
    droppedNames :: [Name]
    droppedNames = map varTToName dropped

-- | Extract Just the Name from a type variable. If the argument Type is not a
-- type variable, return Nothing.
varTToName_maybe :: Type -> Maybe Name
varTToName_maybe (VarT n)   = Just n
varTToName_maybe (SigT t _) = varTToName_maybe t
varTToName_maybe _          = Nothing

-- | Extract the Name from a type variable. If the argument Type is not a
-- type variable, throw an error.
varTToName :: Type -> Name
varTToName = fromMaybe (error "Not a type variable!") . varTToName_maybe

-- | Peel off a kind signature from a Type (if it has one).
unSigT :: Type -> Type
unSigT (SigT t _) = t
unSigT t          = t

-- | Is the given type a variable?
isTyVar :: Type -> Bool
isTyVar (VarT _)   = True
isTyVar (SigT t _) = isTyVar t
isTyVar _          = False

-- | Detect if a Name in a list of provided Names occurs as an argument to some
-- type family. This makes an effort to exclude /oversaturated/ arguments to
-- type families. For instance, if one declared the following type family:
--
-- @
-- type family F a :: Type -> Type
-- @
--
-- Then in the type @F a b@, we would consider @a@ to be an argument to @F@,
-- but not @b@.
isInTypeFamilyApp :: [Name] -> Type -> [Type] -> Q Bool
isInTypeFamilyApp names tyFun tyArgs =
  case tyFun of
    ConT tcName -> go tcName
    _           -> return False
  where
    go :: Name -> Q Bool
    go tcName = do
      info <- reify tcName
      case info of
#if MIN_VERSION_template_haskell(2,11,0)
        FamilyI (OpenTypeFamilyD (TypeFamilyHead _ bndrs _ _)) _
          -> withinFirstArgs bndrs
#elif MIN_VERSION_template_haskell(2,7,0)
        FamilyI (FamilyD TypeFam _ bndrs _) _
          -> withinFirstArgs bndrs
#else
        TyConI (FamilyD TypeFam _ bndrs _)
          -> withinFirstArgs bndrs
#endif

#if MIN_VERSION_template_haskell(2,11,0)
        FamilyI (ClosedTypeFamilyD (TypeFamilyHead _ bndrs _ _) _) _
          -> withinFirstArgs bndrs
#elif MIN_VERSION_template_haskell(2,9,0)
        FamilyI (ClosedTypeFamilyD _ bndrs _ _) _
          -> withinFirstArgs bndrs
#endif

        _ -> return False
      where
        withinFirstArgs :: [a] -> Q Bool
        withinFirstArgs bndrs =
          let firstArgs = take (length bndrs) tyArgs
              argFVs    = freeVariables firstArgs
          in return $ any (`elem` argFVs) names

-- | Are all of the items in a list (which have an ordering) distinct?
--
-- This uses Set (as opposed to nub) for better asymptotic time complexity.
allDistinct :: Ord a => [a] -> Bool
allDistinct = allDistinct' Set.empty
  where
    allDistinct' :: Ord a => Set a -> [a] -> Bool
    allDistinct' uniqs (x:xs)
        | x `Set.member` uniqs = False
        | otherwise            = allDistinct' (Set.insert x uniqs) xs
    allDistinct' _ _           = True

-- | Does the given type mention any of the Names in the list?
mentionsName :: Type -> [Name] -> Bool
mentionsName = go
  where
    go :: Type -> [Name] -> Bool
    go (AppT t1 t2) names = go t1 names || go t2 names
    go (SigT t _k)  names = go t names
#if MIN_VERSION_template_haskell(2,8,0)
                              || go _k names
#endif
    go (VarT n)     names = n `elem` names
    go _            _     = False

-- | Does an instance predicate mention any of the Names in the list?
predMentionsName :: Pred -> [Name] -> Bool
#if MIN_VERSION_template_haskell(2,10,0)
predMentionsName = mentionsName
#else
predMentionsName (ClassP n tys) names = n `elem` names || any (`mentionsName` names) tys
predMentionsName (EqualP t1 t2) names = mentionsName t1 names || mentionsName t2 names
#endif

-- | Construct a type via curried application.
applyTy :: Type -> [Type] -> Type
applyTy = List.foldl' AppT

-- | Fully applies a type constructor to its type variables.
applyTyCon :: Name -> [Type] -> Type
applyTyCon = applyTy . ConT

-- | Split an applied type into its individual components. For example, this:
--
-- @
-- Either Int Char
-- @
--
-- would split to this:
--
-- @
-- [Either, Int, Char]
-- @
unapplyTy :: Type -> (Type, [Type])
unapplyTy ty = go ty ty []
  where
    go :: Type -> Type -> [Type] -> (Type, [Type])
    go _      (AppT ty1 ty2)     args = go ty1 ty1 (ty2:args)
    go origTy (SigT ty' _)       args = go origTy ty' args
#if MIN_VERSION_template_haskell(2,11,0)
    go origTy (InfixT ty1 n ty2) args = go origTy (ConT n `AppT` ty1 `AppT` ty2) args
    go origTy (ParensT ty')      args = go origTy ty' args
#endif
    go origTy _                  args = (origTy, args)

-- | Split a type signature by the arrows on its spine. For example, this:
--
-- @
-- forall a b. (a ~ b) => (a -> b) -> Char -> ()
-- @
--
-- would split to this:
--
-- @
-- (a ~ b, [a -> b, Char, ()])
-- @
uncurryTy :: Type -> (Cxt, [Type])
uncurryTy (AppT (AppT ArrowT t1) t2) =
  let (ctxt, tys) = uncurryTy t2
  in (ctxt, t1:tys)
uncurryTy (SigT t _) = uncurryTy t
uncurryTy (ForallT _ ctxt t) =
  let (ctxt', tys) = uncurryTy t
  in (ctxt ++ ctxt', tys)
uncurryTy t = ([], [t])

-- | Like uncurryType, except on a kind level.
uncurryKind :: Kind -> [Kind]
#if MIN_VERSION_template_haskell(2,8,0)
uncurryKind = snd . uncurryTy
#else
uncurryKind (ArrowK k1 k2) = k1:uncurryKind k2
uncurryKind k              = [k]
#endif

-------------------------------------------------------------------------------
-- Quoted names
-------------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ >= 800
-- With GHC 8.0 or later, we can simply use TemplateHaskellQuotes to quote each
-- name. Life is good.

invariantTypeName :: Name
invariantTypeName = ''Invariant

invariant2TypeName :: Name
invariant2TypeName = ''Invariant2

invmapValName :: Name
invmapValName = 'invmap

invmap2ValName :: Name
invmap2ValName = 'invmap2

invmapConstValName :: Name
invmapConstValName = 'invmapConst

invmap2ConstValName :: Name
invmap2ConstValName = 'invmap2Const

coerceValName :: Name
coerceValName = 'coerce

errorValName :: Name
errorValName = 'error

seqValName :: Name
seqValName = 'seq
#else
-- On pre-8.0 GHCs, we do not have access to the TemplateHaskellQuotes
-- extension, so we construct the Template Haskell names by hand.
-- By manually generating these names we avoid needing to use the
-- TemplateHaskell language extension when compiling the invariant library.
-- This allows the library to be used in stage1 cross-compilers.

invariantPackageKey :: String
# ifdef CURRENT_PACKAGE_KEY
invariantPackageKey = CURRENT_PACKAGE_KEY
# else
invariantPackageKey = "invariant-" ++ showVersion version
# endif

mkInvariantName_tc :: String -> String -> Name
mkInvariantName_tc = mkNameG_tc invariantPackageKey

mkInvariantName_v :: String -> String -> Name
mkInvariantName_v = mkNameG_v invariantPackageKey

invariantTypeName :: Name
invariantTypeName = mkInvariantName_tc "Data.Functor.Invariant" "Invariant"

invariant2TypeName :: Name
invariant2TypeName = mkInvariantName_tc "Data.Functor.Invariant" "Invariant2"

invmapValName :: Name
invmapValName = mkInvariantName_v "Data.Functor.Invariant" "invmap"

invmap2ValName :: Name
invmap2ValName = mkInvariantName_v "Data.Functor.Invariant" "invmap2"

invmapConstValName :: Name
invmapConstValName = mkInvariantName_v "Data.Functor.Invariant.TH.Internal" "invmapConst"

invmap2ConstValName :: Name
invmap2ConstValName = mkInvariantName_v "Data.Functor.Invariant.TH.Internal" "invmap2Const"

coerceValName :: Name
coerceValName = mkNameG_v "ghc-prim" "GHC.Prim" "coerce"

errorValName :: Name
errorValName = mkNameG_v "base" "GHC.Err" "error"

seqValName :: Name
seqValName = mkNameG_v "ghc-prim" "GHC.Prim" "seq"
#endif
