{-# LANGUAGE CPP #-}

{-|
Module:      Data.Functor.Invariant.TH
Copyright:   (C) 2012-2017 Nicolas Frisby, (C) 2015-2017 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Portability: Template Haskell

Functions to mechanically derive 'Invariant' or 'Invariant2' instances,
or to splice 'invmap' or 'invmap2' into Haskell source code. You need to enable
the @TemplateHaskell@ language extension in order to use this module.
-}
module Data.Functor.Invariant.TH (
      -- * @deriveInvariant(2)@
      -- $deriveInvariant
      deriveInvariant
      -- $deriveInvariant2
    , deriveInvariant2
      -- * @makeInvmap(2)@
      -- $make
    , makeInvmap
    , makeInvmap2
    ) where

import           Control.Monad (unless, when)

#if MIN_VERSION_template_haskell(2,8,0) && !(MIN_VERSION_template_haskell(2,10,0))
import           Data.Foldable (foldr')
#endif
import           Data.Functor.Invariant.TH.Internal
import           Data.List
import qualified Data.Map as Map (fromList, keys, lookup, size)
import           Data.Maybe

import           Language.Haskell.TH.Lib
import           Language.Haskell.TH.Ppr
import           Language.Haskell.TH.Syntax

-------------------------------------------------------------------------------
-- User-facing API
-------------------------------------------------------------------------------

{- $deriveInvariant

'deriveInvariant' automatically generates an 'Invariant' instance declaration for a
data type, newtype, or data family instance that has at least one type variable.
This emulates what would (hypothetically) happen if you could attach a @deriving
'Invariant'@ clause to the end of a data declaration. Examples:

@
&#123;-&#35; LANGUAGE TemplateHaskell &#35;-&#125;
import Data.Functor.Invariant.TH

data Pair a = Pair a a
$('deriveInvariant' ''Pair) -- instance Invariant Pair where ...

newtype Alt f a = Alt (f a)
$('deriveInvariant' ''Alt) -- instance Invariant f => Invariant (Alt f) where ...
@

If you are using @template-haskell-2.7.0.0@ or later (i.e., GHC 7.4 or later),
'deriveInvariant' can also be used to derive 'Invariant' instances for data family
instances (which requires the @-XTypeFamilies@ extension). To do so, pass the name of
a data or newtype instance constructor to 'deriveInvariant'.  Note that the generated
code may require the @-XFlexibleInstances@ extension. Some examples:

@
&#123;-&#35; LANGUAGE FlexibleInstances, TemplateHaskell, TypeFamilies &#35;-&#125;
import Data.Functor.Invariant.TH

class AssocClass a b where
    data AssocData a b
instance AssocClass Int b where
    data AssocData Int b = AssocDataInt1 Int | AssocDataInt2 b Int
$('deriveInvariant' 'AssocDataInt1) -- instance Invariant (AssocData Int) where ...
-- Alternatively, one could use $(deriveInvariant 'AssocDataInt2)

data family DataFam a b
newtype instance DataFam () b = DataFamB b
$('deriveInvariant' 'DataFamB) -- instance Invariant (DataFam ())
@

Note that there are some limitations:

* The 'Name' argument to 'deriveInvariant' must not be a type synonym.

* With 'deriveInvariant', the argument's last type variable must be of kind @*@.
  For other ones, type variables of kind @* -> *@ are assumed to require an 'Invariant'
  context. For more complicated scenarios, use 'makeInvmap'.

* If using the @-XDatatypeContexts@, @-XExistentialQuantification@, or @-XGADTs@
  extensions, a constraint cannot mention the last type variable. For example,
  @data Illegal a where I :: Ord a => a -> Illegal a@ cannot have a derived
  'Invariant' instance.

* If the last type variable is used within a data field of a constructor, it must only
  be used in the last argument of the data type constructor. For example, @data Legal a
  = Legal (Either Int a)@ can have a derived 'Invariant' instance, but @data Illegal a =
  Illegal (Either a a)@ cannot.

* Data family instances must be able to eta-reduce the last type variable. In other
  words, if you have a instance of the form:

  @
  data family Family a1 ... an t
  data instance Family e1 ... e2 v = ...
  @

  Then the following conditions must hold:

  1. @v@ must be a type variable.
  2. @v@ must not be mentioned in any of @e1@, ..., @e2@.

-}

-- | Generates an 'Invariant' instance declaration for the given data type or data
-- family instance.
deriveInvariant :: Name -> Q [Dec]
deriveInvariant = deriveInvariantClass Invariant

{- $deriveInvariant2

'deriveInvariant2' automatically generates an 'Invariant2' instance declaration for
a data type, newtype, or data family instance that has at least two type variables.
This emulates what would (hypothetically) happen if you could attach a @deriving
'Invariant2'@ clause to the end of a data declaration. Examples:

@
&#123;-&#35; LANGUAGE TemplateHaskell &#35;-&#125;
import Data.Functor.Invariant.TH

data OneOrNone a b = OneL a | OneR b | None
$('deriveInvariant2' ''OneOrNone) -- instance Invariant2 OneOrNone where ...

newtype Alt2 f a b = Alt2 (f a b)
$('deriveInvariant2' ''Alt2) -- instance Invariant2 f => Invariant2 (Alt2 f) where ...
@

The same restrictions that apply to 'deriveInvariant' also apply to 'deriveInvariant2',
with some caveats:

* With 'deriveInvariant2', the last type variables must both be of kind @*@. For other
  ones, type variables of kind @* -> *@ are assumed to require an 'Invariant'
  constraint, and type variables of kind @* -> * -> *@ are assumed to require an
  'Invariant2' constraint. For more complicated scenarios, use 'makeInvmap2'.

* If using the @-XDatatypeContexts@, @-XExistentialQuantification@, or @-XGADTs@
  extensions, a constraint cannot mention either of the last two type variables. For
  example, @data Illegal2 a b where I2 :: Ord a => a -> b -> Illegal2 a b@ cannot
  have a derived 'Invariant2' instance.

* If either of the last two type variables is used within a data field of a constructor,
  it must only be used in the last two arguments of the data type constructor. For
  example, @data Legal a b = Legal (Int, Int, a, b)@ can have a derived 'Invariant2'
  instance, but @data Illegal a b = Illegal (a, b, a, b)@ cannot.

* Data family instances must be able to eta-reduce the last two type variables. In other
  words, if you have a instance of the form:

  @
  data family Family a1 ... an t1 t2
  data instance Family e1 ... e2 v1 v2 = ...
  @

  Then the following conditions must hold:

  1. @v1@ and @v2@ must be distinct type variables.
  2. Neither @v1@ not @v2@ must be mentioned in any of @e1@, ..., @e2@.

-}

-- | Generates an 'Invariant2' instance declaration for the given data type or data
-- family instance.
deriveInvariant2 :: Name -> Q [Dec]
deriveInvariant2 = deriveInvariantClass Invariant2

{- $make

There may be scenarios in which you want to @invmap@ over an arbitrary data type or
data family instance without having to make the type an instance of 'Invariant'. For
these cases, this module provides several functions (all prefixed with @make-@) that
splice the appropriate lambda expression into your source code. Example:

This is particularly useful for creating instances for sophisticated data types. For
example, 'deriveInvariant' cannot infer the correct type context for @newtype
HigherKinded f a b c = HigherKinded (f a b c)@, since @f@ is of kind
@* -> * -> * -> *@. However, it is still possible to create an 'Invariant' instance
for @HigherKinded@ without too much trouble using 'makeInvmap':

@
&#123;-&#35; LANGUAGE FlexibleContexts, TemplateHaskell &#35;-&#125;
import Data.Functor.Invariant
import Data.Functor.Invariant.TH

newtype HigherKinded f a b c = HigherKinded (f a b c)

instance Invariant (f a b) => Invariant (HigherKinded f a b) where
    invmap = $(makeInvmap ''HigherKinded)
@

-}

-- | Generates a lambda expression which behaves like 'invmap' (without requiring an
-- 'Invariant' instance).
makeInvmap :: Name -> Q Exp
makeInvmap = makeInvmapClass Invariant

-- | Generates a lambda expression which behaves like 'invmap2' (without requiring an
-- 'Invariant2' instance).
makeInvmap2 :: Name -> Q Exp
makeInvmap2 = makeInvmapClass Invariant2

-------------------------------------------------------------------------------
-- Code generation
-------------------------------------------------------------------------------

-- | Derive an Invariant(2) instance declaration (depending on the InvariantClass
-- argument's value).
deriveInvariantClass :: InvariantClass -> Name -> Q [Dec]
deriveInvariantClass iClass name = withType name fromCons
  where
    fromCons :: Name -> Cxt -> [TyVarBndr] -> [Con] -> Maybe [Type] -> Q [Dec]
    fromCons name' ctxt tvbs cons mbTys = (:[]) `fmap` do
        (instanceCxt, instanceType)
            <- buildTypeInstance iClass name' ctxt tvbs mbTys
        instanceD (return instanceCxt)
                  (return instanceType)
                  (invmapDecs iClass cons)

-- | Generates a declaration defining the primary function corresponding to a
-- particular class (invmap for Invariant and invmap2 for Invariant2).
invmapDecs :: InvariantClass -> [Con] -> [Q Dec]
invmapDecs iClass cons =
    [ funD (invmapName iClass)
           [ clause []
                    (normalB $ makeInvmapForCons iClass cons)
                    []
           ]
    ]

-- | Generates a lambda expression which behaves like invmap (for Invariant),
-- or invmap2 (for Invariant2).
makeInvmapClass :: InvariantClass -> Name -> Q Exp
makeInvmapClass iClass name = withType name fromCons
  where
    fromCons :: Name -> Cxt -> [TyVarBndr] -> [Con] -> Maybe [Type] -> Q Exp
    fromCons name' ctxt tvbs cons mbTys =
        -- We force buildTypeInstance here since it performs some checks for whether
        -- or not the provided datatype can actually have invmap/invmap2
        -- implemented for it, and produces errors if it can't.
        buildTypeInstance iClass name' ctxt tvbs mbTys
          `seq` makeInvmapForCons iClass cons

-- | Generates a lambda expression for invmap(2) for the given constructors.
-- All constructors must be from the same type.
makeInvmapForCons :: InvariantClass -> [Con] -> Q Exp
makeInvmapForCons iClass cons = do
    let numNbs = fromEnum iClass

    value      <- newName "value"
    covMaps    <- newNameList "covMap" numNbs
    contraMaps <- newNameList "contraMap" numNbs

    let mapFuns  = zip covMaps contraMaps
        argNames = concat (transpose [covMaps, contraMaps]) ++ [value]
    lamE (map varP argNames)
        . appsE
        $ [ varE $ invmapConstName iClass
          , if null cons
               then appE (varE errorValName)
                         (stringE $ "Void " ++ nameBase (invmapName iClass))
               else caseE (varE value)
                          (map (makeInvmapForCon iClass mapFuns) cons)
          ] ++ map varE argNames

-- | Generates a lambda expression for invmap(2) for a single constructor.
makeInvmapForCon :: InvariantClass -> [(Name, Name)] -> Con -> Q Match
makeInvmapForCon iClass mapFuns con = do
    let conName = constructorName con
    (ts, tvMap) <- reifyConTys iClass conName mapFuns
    argNames    <- newNameList "arg" $ length ts
    makeInvmapForArgs iClass tvMap conName ts argNames

makeInvmapForArgs :: InvariantClass
                  -> TyVarMap
                  -> Name
                  -> [Type]
                  -> [Name]
                  ->  Q Match
makeInvmapForArgs iClass tvMap conName tys args =
    let mappedArgs :: [Q Exp]
        mappedArgs = zipWith (makeInvmapForArg iClass conName tvMap) tys args
     in match (conP conName $ map varP args)
              (normalB . appsE $ conE conName:mappedArgs)
              []

-- | Generates a lambda expression for invmap(2) for an argument of a constructor.
makeInvmapForArg :: InvariantClass
                 -> Name
                 -> TyVarMap
                 -> Type
                 -> Name
                 -> Q Exp
makeInvmapForArg iClass conName tvis ty tyExpName =
    appE (makeInvmapForType iClass conName tvis True ty) (varE tyExpName)

-- | Generates a lambda expression for invmap(2) for a specific type.
-- The generated expression depends on the number of type variables.
makeInvmapForType :: InvariantClass
                  -> Name
                  -> TyVarMap
                  -> Bool
                  -> Type
                  -> Q Exp
makeInvmapForType _ _ tvMap covariant (VarT tyName) =
    case Map.lookup tyName tvMap of
         Just (covMap, contraMap) ->
             varE $ if covariant then covMap else contraMap
         Nothing -> do -- Produce a lambda expression rather than id, addressing Trac #7436
             x <- newName "x"
             lamE [varP x] $ varE x
makeInvmapForType iClass conName tvMap covariant (SigT ty _) =
    makeInvmapForType iClass conName tvMap covariant ty
makeInvmapForType iClass conName tvMap covariant (ForallT _ _ ty)
    = makeInvmapForType iClass conName tvMap covariant ty
makeInvmapForType iClass conName tvMap covariant ty =
    let tyCon  :: Type
        tyArgs :: [Type]
        tyCon:tyArgs = unapplyTy ty

        numLastArgs :: Int
        numLastArgs = min (fromEnum iClass) (length tyArgs)

        lhsArgs, rhsArgs :: [Type]
        (lhsArgs, rhsArgs) = splitAt (length tyArgs - numLastArgs) tyArgs

        tyVarNames :: [Name]
        tyVarNames = Map.keys tvMap

        doubleMap :: (Bool -> Type -> Q Exp) -> [Type] -> [Q Exp]
        doubleMap _ []     = []
        doubleMap f (t:ts) = f covariant t : f (not covariant) t : doubleMap f ts

        mentionsTyArgs :: Bool
        mentionsTyArgs = any (`mentionsName` tyVarNames) tyArgs

        makeInvmapTuple :: ([Q Pat] -> Q Pat) -> ([Q Exp] -> Q Exp) -> Int -> Q Exp
        makeInvmapTuple mkTupP mkTupE n = do
            x  <- newName "x"
            xs <- newNameList "x" n
            lamE [varP x] $ caseE (varE x)
                [ match (mkTupP $ map varP xs)
                        (normalB . mkTupE $ zipWith makeInvmapTupleField tyArgs xs)
                        []
                ]

        makeInvmapTupleField :: Type -> Name -> Q Exp
        makeInvmapTupleField fieldTy fieldName =
            appE (makeInvmapForType iClass conName tvMap covariant fieldTy) $ varE fieldName

     in case tyCon of
          ArrowT | mentionsTyArgs ->
              let [argTy, resTy] = tyArgs
               in do x <- newName "x"
                     b <- newName "b"
                     lamE [varP x, varP b] $
                       makeInvmapForType iClass conName tvMap covariant resTy `appE` (varE x `appE`
                         (makeInvmapForType iClass conName tvMap (not covariant) argTy `appE` varE b))
#if MIN_VERSION_template_haskell(2,6,0)
          UnboxedTupleT n
            | n > 0 && mentionsTyArgs -> makeInvmapTuple unboxedTupP unboxedTupE n
#endif
          TupleT n
            | n > 0 && mentionsTyArgs -> makeInvmapTuple tupP tupE n
          _ -> do
              itf <- isTyFamily tyCon
              if any (`mentionsName` tyVarNames) lhsArgs || (itf && mentionsTyArgs)
                   then outOfPlaceTyVarError conName tyVarNames
                   else if any (`mentionsName` tyVarNames) rhsArgs
                        then appsE $
                             ( varE (invmapName (toEnum numLastArgs))
                             : doubleMap (makeInvmapForType iClass conName tvMap) rhsArgs
                             )
                        else do x <- newName "x"
                                lamE [varP x] $ varE x

-------------------------------------------------------------------------------
-- Template Haskell reifying and AST manipulation
-------------------------------------------------------------------------------

-- | Extracts a plain type constructor's information.
-- | Boilerplate for top level splices.
--
-- The given Name must meet one of two criteria:
--
-- 1. It must be the name of a type constructor of a plain data type or newtype.
-- 2. It must be the name of a data family instance or newtype instance constructor.
--
-- Any other value will result in an exception.
withType :: Name
         -> (Name -> Cxt -> [TyVarBndr] -> [Con] -> Maybe [Type] -> Q a)
         -> Q a
withType name f = do
  info <- reify name
  case info of
    TyConI dec ->
      case dec of
        DataD ctxt _ tvbs
#if MIN_VERSION_template_haskell(2,11,0)
              _
#endif
              cons _ -> f name ctxt tvbs cons Nothing
        NewtypeD ctxt _ tvbs
#if MIN_VERSION_template_haskell(2,11,0)
                 _
#endif
                 con _ -> f name ctxt tvbs [con] Nothing
        _ -> error $ ns ++ "Unsupported type: " ++ show dec
#if MIN_VERSION_template_haskell(2,7,0)
# if MIN_VERSION_template_haskell(2,11,0)
    DataConI _ _ parentName   -> do
# else
    DataConI _ _ parentName _ -> do
# endif
      parentInfo <- reify parentName
      case parentInfo of
# if MIN_VERSION_template_haskell(2,11,0)
        FamilyI (DataFamilyD _ tvbs _) decs ->
# else
        FamilyI (FamilyD DataFam _ tvbs _) decs ->
# endif
          let instDec = flip find decs $ \dec -> case dec of
                DataInstD _ _ _
# if MIN_VERSION_template_haskell(2,11,0)
                          _
# endif
                          cons _ -> any ((name ==) . constructorName) cons
                NewtypeInstD _ _ _
# if MIN_VERSION_template_haskell(2,11,0)
                             _
# endif
                             con _ -> name == constructorName con
                _ -> error $ ns ++ "Must be a data or newtype instance."
           in case instDec of
                Just (DataInstD ctxt _ instTys
# if MIN_VERSION_template_haskell(2,11,0)
                                _
# endif
                                cons _)
                  -> f parentName ctxt tvbs cons $ Just instTys
                Just (NewtypeInstD ctxt _ instTys
# if MIN_VERSION_template_haskell(2,11,0)
                                   _
# endif
                                   con _)
                  -> f parentName ctxt tvbs [con] $ Just instTys
                _ -> error $ ns ++
                  "Could not find data or newtype instance constructor."
        _ -> error $ ns ++ "Data constructor " ++ show name ++
          " is not from a data family instance constructor."
# if MIN_VERSION_template_haskell(2,11,0)
    FamilyI DataFamilyD{} _ ->
# else
    FamilyI (FamilyD DataFam _ _ _) _ ->
# endif
      error $ ns ++
        "Cannot use a data family name. Use a data family instance constructor instead."
    _ -> error $ ns ++ "The name must be of a plain data type constructor, "
                    ++ "or a data family instance constructor."
#else
    DataConI{} -> dataConIError
    _          -> error $ ns ++ "The name must be of a plain type constructor."
#endif
  where
    ns :: String
    ns = "Data.Functor.Invariant.TH.withType: "

-- | Deduces the instance context and head for an instance.
buildTypeInstance :: InvariantClass
                  -- ^ Invariant or Invariant2
                  -> Name
                  -- ^ The type constructor or data family name
                  -> Cxt
                  -- ^ The datatype context
                  -> [TyVarBndr]
                  -- ^ The type variables from the data type/data family declaration
                  -> Maybe [Type]
                  -- ^ 'Just' the types used to instantiate a data family instance,
                  -- or 'Nothing' if it's a plain data type
                  -> Q (Cxt, Type)
-- Plain data type/newtype case
buildTypeInstance iClass tyConName dataCxt tvbs Nothing =
    let varTys :: [Type]
        varTys = map tvbToType tvbs
    in buildTypeInstanceFromTys iClass tyConName dataCxt varTys False
-- Data family instance case
--
-- The CPP is present to work around a couple of annoying old GHC bugs.
-- See Note [Polykinded data families in Template Haskell]
buildTypeInstance iClass parentName dataCxt tvbs (Just instTysAndKinds) = do
#if !(MIN_VERSION_template_haskell(2,8,0)) || MIN_VERSION_template_haskell(2,10,0)
    let instTys :: [Type]
        instTys = zipWith stealKindForType tvbs instTysAndKinds
#else
    let kindVarNames :: [Name]
        kindVarNames = nub $ concatMap (tyVarNamesOfType . tvbKind) tvbs

        numKindVars :: Int
        numKindVars = length kindVarNames

        givenKinds, givenKinds' :: [Kind]
        givenTys                :: [Type]
        (givenKinds, givenTys) = splitAt numKindVars instTysAndKinds
        givenKinds' = map sanitizeStars givenKinds

        -- A GHC 7.6-specific bug requires us to replace all occurrences of
        -- (ConT GHC.Prim.*) with StarT, or else Template Haskell will reject it.
        -- Luckily, (ConT GHC.Prim.*) only seems to occur in this one spot.
        sanitizeStars :: Kind -> Kind
        sanitizeStars = go
          where
            go :: Kind -> Kind
            go (AppT t1 t2)                 = AppT (go t1) (go t2)
            go (SigT t k)                   = SigT (go t) (go k)
            go (ConT n) | n == starKindName = StarT
            go t                            = t

    -- If we run this code with GHC 7.8, we might have to generate extra type
    -- variables to compensate for any type variables that Template Haskell
    -- eta-reduced away.
    -- See Note [Polykinded data families in Template Haskell]
    xTypeNames <- newNameList "tExtra" (length tvbs - length givenTys)

    let xTys   :: [Type]
        xTys = map VarT xTypeNames
        -- ^ Because these type variables were eta-reduced away, we can only
        --   determine their kind by using stealKindForType. Therefore, we mark
        --   them as VarT to ensure they will be given an explicit kind annotation
        --   (and so the kind inference machinery has the right information).

        substNamesWithKinds :: [(Name, Kind)] -> Type -> Type
        substNamesWithKinds nks t = foldr' (uncurry substNameWithKind) t nks

        -- The types from the data family instance might not have explicit kind
        -- annotations, which the kind machinery needs to work correctly. To
        -- compensate, we use stealKindForType to explicitly annotate any
        -- types without kind annotations.
        instTys :: [Type]
        instTys = map (substNamesWithKinds (zip kindVarNames givenKinds'))
                  -- ^ Note that due to a GHC 7.8-specific bug
                  --   (see Note [Polykinded data families in Template Haskell]),
                  --   there may be more kind variable names than there are kinds
                  --   to substitute. But this is OK! If a kind is eta-reduced, it
                  --   means that is was not instantiated to something more specific,
                  --   so we need not substitute it. Using stealKindForType will
                  --   grab the correct kind.
                $ zipWith stealKindForType tvbs (givenTys ++ xTys)
#endif
    buildTypeInstanceFromTys iClass parentName dataCxt instTys True

-- For the given Types, generate an instance context and head. Coming up with
-- the instance type isn't as simple as dropping the last types, as you need to
-- be wary of kinds being instantiated with *.
-- See Note [Type inference in derived instances]
buildTypeInstanceFromTys :: InvariantClass
                         -- ^ Invariant or Invariant2
                         -> Name
                         -- ^ The type constructor or data family name
                         -> Cxt
                         -- ^ The datatype context
                         -> [Type]
                         -- ^ The types to instantiate the instance with
                         -> Bool
                         -- ^ True if it's a data family, False otherwise
                         -> Q (Cxt, Type)
buildTypeInstanceFromTys iClass tyConName dataCxt varTysOrig isDataFamily = do
    -- Make sure to expand through type/kind synonyms! Otherwise, the
    -- eta-reduction check might get tripped up over type variables in a
    -- synonym that are actually dropped.
    -- (See GHC Trac #11416 for a scenario where this actually happened.)
    varTysExp <- mapM expandSyn varTysOrig

    let remainingLength :: Int
        remainingLength = length varTysOrig - fromEnum iClass

        droppedTysExp :: [Type]
        droppedTysExp = drop remainingLength varTysExp

        droppedStarKindStati :: [StarKindStatus]
        droppedStarKindStati = map canRealizeKindStar droppedTysExp

    -- Check there are enough types to drop and that all of them are either of
    -- kind * or kind k (for some kind variable k). If not, throw an error.
    when (remainingLength < 0 || any (== NotKindStar) droppedStarKindStati) $
      derivingKindError iClass tyConName

    let droppedKindVarNames :: [Name]
        droppedKindVarNames = catKindVarNames droppedStarKindStati

        -- Substitute kind * for any dropped kind variables
        varTysExpSubst :: [Type]
        varTysExpSubst = map (substNamesWithKindStar droppedKindVarNames) varTysExp

        remainingTysExpSubst, droppedTysExpSubst :: [Type]
        (remainingTysExpSubst, droppedTysExpSubst) =
          splitAt remainingLength varTysExpSubst

        -- All of the type variables mentioned in the dropped types
        -- (post-synonym expansion)
        droppedTyVarNames :: [Name]
        droppedTyVarNames = concatMap tyVarNamesOfType droppedTysExpSubst

    -- If any of the dropped types were polykinded, ensure that there are of kind *
    -- after substituting * for the dropped kind variables. If not, throw an error.
    unless (all hasKindStar droppedTysExpSubst) $
      derivingKindError iClass tyConName

    let preds    :: [Maybe Pred]
        kvNames  :: [[Name]]
        kvNames' :: [Name]
        -- Derive instance constraints (and any kind variables which are specialized
        -- to * in those constraints)
        (preds, kvNames) = unzip $ map (deriveConstraint iClass) remainingTysExpSubst
        kvNames' = concat kvNames

        -- Substitute the kind variables specialized in the constraints with *
        remainingTysExpSubst' :: [Type]
        remainingTysExpSubst' =
          map (substNamesWithKindStar kvNames') remainingTysExpSubst

        -- We now substitute all of the specialized-to-* kind variable names with
        -- *, but in the original types, not the synonym-expanded types. The reason
        -- we do this is a superficial one: we want the derived instance to resemble
        -- the datatype written in source code as closely as possible. For example,
        -- for the following data family instance:
        --
        --   data family Fam a
        --   newtype instance Fam String = Fam String
        --
        -- We'd want to generate the instance:
        --
        --   instance C (Fam String)
        --
        -- Not:
        --
        --   instance C (Fam [Char])
        remainingTysOrigSubst :: [Type]
        remainingTysOrigSubst =
          map (substNamesWithKindStar (union droppedKindVarNames kvNames'))
            $ take remainingLength varTysOrig

        remainingTysOrigSubst' :: [Type]
        -- See Note [Kind signatures in derived instances] for an explanation
        -- of the isDataFamily check.
        remainingTysOrigSubst' =
          if isDataFamily
             then remainingTysOrigSubst
             else map unSigT remainingTysOrigSubst

        instanceCxt :: Cxt
        instanceCxt = catMaybes preds

        instanceType :: Type
        instanceType = AppT (ConT $ invariantClassName iClass)
                     $ applyTyCon tyConName remainingTysOrigSubst'

    -- If the datatype context mentions any of the dropped type variables,
    -- we can't derive an instance, so throw an error.
    when (any (`predMentionsName` droppedTyVarNames) dataCxt) $
      datatypeContextError tyConName instanceType
    -- Also ensure the dropped types can be safely eta-reduced. Otherwise,
    -- throw an error.
    unless (canEtaReduce remainingTysExpSubst' droppedTysExpSubst) $
      etaReductionError instanceType
    return (instanceCxt, instanceType)

-- | Attempt to derive a constraint on a Type. If successful, return
-- Just the constraint and any kind variable names constrained to *.
-- Otherwise, return Nothing and the empty list.
--
-- See Note [Type inference in derived instances] for the heuristics used to
-- come up with constraints.
deriveConstraint :: InvariantClass -> Type -> (Maybe Pred, [Name])
deriveConstraint iClass t
  | not (isTyVar t) = (Nothing, [])
  | otherwise = case hasKindVarChain 1 t of
      Just ns | iClass >= Invariant
              -> (Just (applyClass invariantTypeName tName), ns)
      _ -> case hasKindVarChain 2 t of
                Just ns | iClass == Invariant2
                        -> (Just (applyClass invariant2TypeName tName), ns)
                _       -> (Nothing, [])
  where
    tName :: Name
    tName = varTToName t

{-
Note [Polykinded data families in Template Haskell]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In order to come up with the correct instance context and head for an instance, e.g.,
  instance C a => C (Data a) where ...
We need to know the exact types and kinds used to instantiate the instance. For
plain old datatypes, this is simple: every type must be a type variable, and
Template Haskell reliably tells us the type variables and their kinds.
Doing the same for data families proves to be much harder for three reasons:
1. On any version of Template Haskell, it may not tell you what an instantiated
   type's kind is. For instance, in the following data family instance:
     data family Fam (f :: * -> *) (a :: *)
     data instance Fam f a
   Then if we use TH's reify function, it would tell us the TyVarBndrs of the
   data family declaration are:
     [KindedTV f (AppT (AppT ArrowT StarT) StarT),KindedTV a StarT]
   and the instantiated types of the data family instance are:
     [VarT f1,VarT a1]
   We can't just pass [VarT f1,VarT a1] to buildTypeInstanceFromTys, since we
   have no way of knowing their kinds. Luckily, the TyVarBndrs tell us what the
   kind is in case an instantiated type isn't a SigT, so we use the stealKindForType
   function to ensure all of the instantiated types are SigTs before passing them
   to buildTypeInstanceFromTys.
2. On GHC 7.6 and 7.8, a bug is present in which Template Haskell lists all of
   the specified kinds of a data family instance efore any of the instantiated
   types. Fortunately, this is easy to deal with: you simply count the number of
   distinct kind variables in the data family declaration, take that many elements
   from the front of the  Types list of the data family instance, substitute the
   kind variables with their respective instantiated kinds (which you took earlier),
   and proceed as normal.
3. On GHC 7.8, an even uglier bug is present (GHC Trac #9692) in which Template
   Haskell might not even list all of the Types of a data family instance, since
   they are eta-reduced away! And yes, kinds can be eta-reduced too.
   The simplest workaround is to count how many instantiated types are missing from
   the list and generate extra type variables to use in their place. Luckily, we
   needn't worry much if its kind was eta-reduced away, since using stealKindForType
   will get it back.
Note [Kind signatures in derived instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It is possible to put explicit kind signatures into the derived instances, e.g.,
  instance C a => C (Data (f :: * -> *)) where ...
But it is preferable to avoid this if possible. If we come up with an incorrect
kind signature (which is entirely possible, since our type inferencer is pretty
unsophisticated - see Note [Type inference in derived instances]), then GHC will
flat-out reject the instance, which is quite unfortunate.
Plain old datatypes have the advantage that you can avoid using any kind signatures
at all in their instances. This is because a datatype declaration uses all type
variables, so the types that we use in a derived instance uniquely determine their
kinds. As long as we plug in the right types, the kind inferencer can do the rest
of the work. For this reason, we use unSigT to remove all kind signatures before
splicing in the instance context and head.
Data family instances are trickier, since a data family can have two instances that
are distinguished by kind alone, e.g.,
  data family Fam (a :: k)
  data instance Fam (a :: * -> *)
  data instance Fam (a :: *)
If we dropped the kind signatures for C (Fam a), then GHC will have no way of
knowing which instance we are talking about. To avoid this scenario, we always
include explicit kind signatures in data family instances. There is a chance that
the inferred kind signatures will be incorrect, but if so, we can always fall back
on the make- functions.
Note [Type inference in derived instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Type inference is can be tricky to get right, and we want to avoid recreating the
entirety of GHC's type inferencer in Template Haskell. For this reason, we will
probably never come up with derived instance contexts that are as accurate as
GHC's. But that doesn't mean we can't do anything! There are a couple of simple
things we can do to make instance contexts that work for 80% of use cases:
1. If one of the last type parameters is polykinded, then its kind will be
   specialized to * in the derived instance. We note what kind variable the type
   parameter had and substitute it with * in the other types as well. For example,
   imagine you had
     data Data (a :: k) (b :: k) (c :: k)
   Then you'd want to derived instance to be:
     instance C (Data (a :: *))
   Not:
     instance C (Data (a :: k))
2. We naïvely come up with instance constraints using the following criteria:
   (i)  If there's a type parameter n of kind k1 -> k2 (where k1/k2 are * or kind
        variables), then generate an Invariant n constraint, and if k1/k2 are kind
        variables, then substitute k1/k2 with * elsewhere in the types. We must
        consider the case where they are kind variables because you might have a
        scenario like this:
          newtype Compose (f :: k3 -> *) (g :: k1 -> k2 -> k3) (a :: k1) (b :: k2)
            = Compose (f (g a b))
        Which would have a derived Invariant2 instance of:
          instance (Invariant f, Invariant2 g) => Invariant2 (Compose f g) where ...
   (ii) If there's a type parameter n of kind k1 -> k2 -> k3 (where k1/k2/k3 are
        * or kind variables), then generate a Invariant2 n constraint and perform
        kind substitution as in the other case.
-}

-- Determines the types of a constructor's arguments as well as the last type
-- parameters (along with their map functions), expanding through any type synonyms.
-- The type parameters are determined on a constructor-by-constructor basis since
-- they may be refined to be particular types in a GADT.
reifyConTys :: InvariantClass
            -> Name
            -> [(Name, Name)]
            -> Q ([Type], TyVarMap)
reifyConTys iClass conName maps = do
    info          <- reify conName
    (ctxt, uncTy) <- case info of
        DataConI _ ty _
#if !(MIN_VERSION_template_haskell(2,11,0))
                 _
#endif
                 -> fmap uncurryTy (expandSyn ty)
        _ -> error "Must be a data constructor"
    let (argTys, [resTy]) = splitAt (length uncTy - 1) uncTy
        unapResTy = unapplyTy resTy
        numToDrop = fromEnum iClass
        -- If one of the last type variables is refined to a particular type
        -- (i.e., not truly polymorphic), we mark it with Nothing and filter
        -- it out later, since we only apply map functions to arguments of
        -- a type that is (1) one of the last type variables, and (2)
        -- of a truly polymorphic type.
        mbTvNames = map varTToName_maybe $
                        drop (length unapResTy - numToDrop) unapResTy
        tvMap = Map.fromList
                    . catMaybes -- Drop refined types
                    $ zipWith (\mbTvName mapFuns ->
                                  fmap (\tvName -> (tvName, mapFuns)) mbTvName)
                              mbTvNames maps
    if any (`predMentionsName` Map.keys tvMap) ctxt
         || Map.size tvMap < numToDrop
       then existentialContextError conName
       else return (argTys, tvMap)

-------------------------------------------------------------------------------
-- Error messages
-------------------------------------------------------------------------------

-- | Either the given data type doesn't have enough type variables, or one of
-- the type variables to be eta-reduced cannot realize kind *.
derivingKindError :: InvariantClass -> Name -> a
derivingKindError iClass tyConName = error
    . showString "Cannot derive well-kinded instance of form ‘"
    . showString className
    . showChar ' '
    . showParen True
      ( showString (nameBase tyConName)
      . showString " ..."
      )
    . showString "‘\n\tClass "
    . showString className
    . showString " expects an argument of kind "
    . showString (pprint . createKindChain $ fromEnum iClass)
    $ ""
  where
    className :: String
    className = nameBase $ invariantClassName iClass

-- | The data type has a DatatypeContext which mentions one of the eta-reduced
-- type variables.
datatypeContextError :: Name -> Type -> a
datatypeContextError dataName instanceType = error
    . showString "Can't make a derived instance of ‘"
    . showString (pprint instanceType)
    . showString "‘:\n\tData type ‘"
    . showString (nameBase dataName)
    . showString "‘ must not have a class context involving the last type argument(s)"
    $ ""

-- | The data type has an existential constraint which mentions one of the
-- eta-reduced type variables.
existentialContextError :: Name -> a
existentialContextError conName = error
    . showString "Constructor ‘"
    . showString (nameBase conName)
    . showString "‘ must be truly polymorphic in the last argument(s) of the data type"
    $ ""

-- | The data type mentions one of the n eta-reduced type variables in a place other
-- than the last nth positions of a data type in a constructor's field.
outOfPlaceTyVarError :: Name -> a
outOfPlaceTyVarError conName = error
  . showString "Constructor ‘"
  . showString (nameBase conName)
  . showString "‘ must only use its last two type variable(s) within"
  . showString " the last two argument(s) of a data type"
  $ ""

-- | One of the last type variables cannot be eta-reduced (see the canEtaReduce
-- function for the criteria it would have to meet).
etaReductionError :: Type -> a
etaReductionError instanceType = error $
    "Cannot eta-reduce to an instance of form \n\tinstance (...) => "
    ++ pprint instanceType

#if !(MIN_VERSION_template_haskell(2,7,0))
-- | Template Haskell didn't list all of a data family's instances upon reification
-- until template-haskell-2.7.0.0, which is necessary for a derived Invariant instance
-- to work.
dataConIError :: a
dataConIError = error
    . showString "Cannot use a data constructor."
    . showString "\n\t(Note: if you are trying to derive Invariant for a type family,"
    . showString "\n\tuse GHC >= 7.4 instead.)"
    $ ""
#endif
