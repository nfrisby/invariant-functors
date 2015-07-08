{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-|
Module:      Data.Functor.Invariant.TH
Copyright:   (C) 2012-2015 Nicolas Frisby, (C) 2015 Ryan Scott
License:     BSD-style (see the file LICENSE)
Maintainer:  Ryan Scott
Portability: Template Haskell

Functions to mechanically derive 'Invariant' or 'Invariant2' instances,
or to splice 'invmap' or 'invmap2' into Haskell source code. You need to enable
the @TemplateHaskell@ language extension in order to use this module.
-}
module Data.Functor.Invariant.TH (
      -- $deriveInvariant
      deriveInvariant
      -- $deriveInvariant2
    , deriveInvariant2
      -- $make
    , makeInvmap
    , makeInvmap2
    ) where

import           Data.Function (on)
import           Data.Functor.Invariant (Invariant(..), Invariant2(..))
import           Data.List (foldl', transpose)
#if MIN_VERSION_template_haskell(2,7,0)
import           Data.List (find)
#endif
import qualified Data.Map as Map (fromList, lookup)
import           Data.Map (Map)
import           Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import           Data.Set (Set)

import           Language.Haskell.TH.Lib
import           Language.Haskell.TH.Ppr hiding (appPrec)
import           Language.Haskell.TH.Syntax

-------------------------------------------------------------------------------
-- User-facing API
-------------------------------------------------------------------------------

{- $deriveInvariant

'deriveInvariant' automatically generates an 'Invariant' instance declaration for a
data type, a newtype, or a data family instance that has at least one type variable.
This emulates what would (hypothetically) happen if you could attach a @deriving
'Invariant'@ clause to the end of a data declaration. Examples:

@
&#123;-&#35; LANGUAGE TemplateHaskell &#35;-&#125;
import Data.Functor.Invariant.TH (deriveInvariant)

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
import Data.Functor.Invariant.TH (deriveInvariant)

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

* In GHC 7.8, a bug exists that can cause problems when a data family declaration and
  one of its data instances use different type variables, e.g.,

  @
  data family Foo a b c
  data instance Foo Int y z = Foo Int y z
  $(deriveInvariant 'Foo)
  @

  To avoid this issue, it is recommened that you use the same type variables in the
  same positions in which they appeared in the data family declaration:

  @
  data family Foo a b c
  data instance Foo Int b c = Foo Int b c
  $(deriveInvariant 'Foo)
  @

-}

-- | Generates an 'Invariant' instance declaration for the given data type or data
-- family instance.
deriveInvariant :: Name -> Q [Dec]
deriveInvariant = deriveInvariantClass Invariant

{- $deriveInvariant2

'deriveInvariant2' automatically generates an 'Invariant2' instance declaration for
a data type, a newtype, or a data family instance that has at least two type variables.
This emulates what would (hypothetically) happen if you could attach a @deriving
'Invariant2'@ clause to the end of a data declaration. Examples:

@
&#123;-&#35; LANGUAGE TemplateHaskell &#35;-&#125;
import Data.Functor.Invariant.TH (deriveInvariant2)

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

@
&#123;-&#35; LANGUAGE TemplateHaskell &#35;-&#125;
import Data.Functor.Invariant.TH (makeInvmap)

newtype Identity a = Identity a

mapIdentity :: (a -> b) -> Identity a -> Identity b
mapIdentity f = $(makeInvmap ''Identity) f undefined
@

@make-@ functions are also useful for creating 'Invariant' instances for data types
with sophisticated type parameters. For example, 'deriveInvariant' cannot infer the
correct type context for @newtype HigherKinded f a b c = HigherKinded (f a b c)@,
since @f@ is of kind @* -> * -> * -> *@. However, it is still possible to create an
'Invariant' instance for @HigherKinded@ without too much trouble using 'makeInvmap':

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
deriveInvariantClass iClass tyConName = do
    info <- reify tyConName
    case info of
        TyConI{} -> deriveInvariantPlainTy iClass tyConName
#if MIN_VERSION_template_haskell(2,7,0)
        DataConI{} -> deriveInvariantDataFamInst iClass tyConName
        FamilyI (FamilyD DataFam _ _ _) _ ->
            error $ ns ++ "Cannot use a data family name. Use a data family instance constructor instead."
        FamilyI (FamilyD TypeFam _ _ _) _ ->
            error $ ns ++ "Cannot use a type family name."
        _ -> error $ ns ++ "The name must be of a plain type constructor or data family instance constructor."
#else
        DataConI{} -> dataConIError
        _          -> error $ ns ++ "The name must be of a plain type constructor."
#endif
  where
    ns :: String
    ns = "Data.Functor.Invariant.TH.deriveInvariant: "

-- | Generates an Invariant(2) instance declaration for a plain type constructor.
deriveInvariantPlainTy :: InvariantClass -> Name -> Q [Dec]
deriveInvariantPlainTy iClass tyConName =
    withTyCon tyConName fromCons
  where
    className :: Name
    className = invariantClassNameTable iClass

    fromCons :: Cxt -> [TyVarBndr] -> [Con] -> Q [Dec]
    fromCons ctxt tvbs cons = (:[]) `fmap`
        instanceD (return instanceCxt)
                  (return $ AppT (ConT className) instanceType)
                  (invmapDecs droppedNbs cons)
      where
        (instanceCxt, instanceType, droppedNbs) =
            cxtAndTypePlainTy iClass tyConName ctxt tvbs

#if MIN_VERSION_template_haskell(2,7,0)
-- | Generates an Invariant(2) instance declaration for a data family instance
-- constructor.
deriveInvariantDataFamInst :: InvariantClass -> Name -> Q [Dec]
deriveInvariantDataFamInst iClass dataFamInstName =
    withDataFamInstCon dataFamInstName fromDec
  where
    className :: Name
    className = invariantClassNameTable iClass

    fromDec :: [TyVarBndr] -> Cxt -> Name -> [Type] -> [Con] -> Q [Dec]
    fromDec famTvbs ctxt parentName instTys cons = (:[]) `fmap`
        instanceD (return instanceCxt)
                  (return $ AppT (ConT className) instanceType)
                  (invmapDecs droppedNbs cons)
      where
        (instanceCxt, instanceType, droppedNbs) =
            cxtAndTypeDataFamInstCon iClass parentName ctxt famTvbs instTys
#endif

-- | Generates a declaration defining the primary function corresponding to a
-- particular class (invmap for Invariant and invmap2 for Invariant2).
invmapDecs :: [NameBase] -> [Con] -> [Q Dec]
invmapDecs nbs cons =
    [ funD classFuncName
           [ clause []
                    (normalB $ makeInvmapForCons nbs cons)
                    []
           ]
    ]
  where
    classFuncName :: Name
    classFuncName  = invmapNameTable . toEnum $ length nbs

-- | Generates a lambda expression which behaves like invmap (for Invariant),
-- or invmap2 (for Invariant2).
makeInvmapClass :: InvariantClass -> Name -> Q Exp
makeInvmapClass iClass tyConName = do
    info <- reify tyConName
    case info of
        TyConI{} -> withTyCon tyConName $ \ctxt tvbs decs ->
            let nbs = thd3 $ cxtAndTypePlainTy iClass tyConName ctxt tvbs
             in makeInvmapForCons nbs decs
#if MIN_VERSION_template_haskell(2,7,0)
        DataConI{} -> withDataFamInstCon tyConName $ \famTvbs ctxt parentName instTys cons ->
            let nbs = thd3 $ cxtAndTypeDataFamInstCon iClass parentName ctxt famTvbs instTys
             in makeInvmapForCons nbs cons
        FamilyI (FamilyD DataFam _ _ _) _ ->
            error $ ns ++ "Cannot use a data family name. Use a data family instance constructor instead."
        FamilyI (FamilyD TypeFam _ _ _) _ ->
            error $ ns ++ "Cannot use a type family name."
        _ -> error $ ns ++ "The name must be of a plain type constructor or data family instance constructor."
#else
        DataConI{} -> dataConIError
        _          -> error $ ns ++ "The name must be of a plain type constructor."
#endif
  where
    ns :: String
    ns = "Data.Functor.Invariant.TH.makeInvmap: "

-- | Generates a lambda expression for invmap(2) for the given constructors.
-- All constructors must be from the same type.
makeInvmapForCons :: [NameBase] -> [Con] -> Q Exp
makeInvmapForCons nbs cons = do
    let numNbs = length nbs

    value      <- newName "value"
    covMaps    <- newNameList "covMap" numNbs
    contraMaps <- newNameList "contraMap" numNbs

    let tvis     = zip3 nbs covMaps contraMaps
        iClass   = toEnum numNbs
        argNames = concat (transpose [covMaps, contraMaps]) ++ [value]
    lamE (map varP argNames)
        . appsE
        $ [ varE $ invmapConstNameTable iClass
          , if null cons
               then appE (varE 'error)
                         (stringE $ "Void " ++ nameBase (invmapNameTable iClass))
               else caseE (varE value)
                          (map (makeInvmapForCon iClass tvis) cons)
          ] ++ map varE argNames

-- | Generates a lambda expression for invmap(2) for a single constructor.
makeInvmapForCon :: InvariantClass -> [TyVarInfo] -> Con -> Q Match
makeInvmapForCon iClass tvis (NormalC conName tys) = do
    args <- newNameList "arg" $ length tys
    let argTys = map snd tys
    makeInvmapForArgs iClass tvis conName argTys args
makeInvmapForCon iClass tvis (RecC conName tys) = do
    args <- newNameList "arg" $ length tys
    let argTys = map thd3 tys
    makeInvmapForArgs iClass tvis conName argTys args
makeInvmapForCon iClass tvis (InfixC (_, argTyL) conName (_, argTyR)) = do
    argL <- newName "argL"
    argR <- newName "argR"
    makeInvmapForArgs iClass tvis conName [argTyL, argTyR] [argL, argR]
makeInvmapForCon iClass tvis (ForallC tvbs faCxt con) =
    if any (`predMentionsNameBase` map fst3 tvis) faCxt
       then existentialContextError . nameBase $ constructorName con
       else makeInvmapForCon iClass (removeForalled tvbs tvis) con

makeInvmapForArgs :: InvariantClass
                  -> [TyVarInfo]
                  -> Name
                  -> [Type]
                  -> [Name]
                  ->  Q Match
makeInvmapForArgs iClass tvis conName tys args =
    let mappedArgs :: [Q Exp]
        mappedArgs = zipWith (makeInvmapForArg iClass (nameBase conName) tvis) tys args
     in match (conP conName $ map varP args)
              (normalB . appsE $ conE conName:mappedArgs)
              []

-- | Generates a lambda expression for invmap(2) for an argument of a constructor.
makeInvmapForArg :: InvariantClass
                 -> String
                 -> [TyVarInfo]
                 -> Type
                 -> Name
                 -> Q Exp
makeInvmapForArg iClass conName tvis ty tyExpName = do
    ty' <- expandSyn ty
    makeInvmapForArg' iClass conName tvis ty' tyExpName

-- | Generates a lambda expression for invmap(2) for an argument of a
-- constructor, after expanding all type synonyms.
makeInvmapForArg' :: InvariantClass
                  -> String
                  -> [TyVarInfo]
                  -> Type
                  -> Name
                  -> Q Exp
makeInvmapForArg' iClass conName tvis ty tyExpName =
    appE (makeInvmapForType iClass conName tvis True ty) (varE tyExpName)

-- | Generates a lambda expression for invmap(2) for a specific type.
-- The generated expression depends on the number of type variables.
makeInvmapForType :: InvariantClass
                  -> String
                  -> [TyVarInfo]
                  -> Bool
                  -> Type
                  -> Q Exp
makeInvmapForType _ _ tvis covariant (VarT tyName) =
    case lookup2 (NameBase tyName) tvis of
         Just (covMap, contraMap) ->
             varE $ if covariant then covMap else contraMap
         Nothing -> [| \x -> x |] -- Produce a lambda expression rather than id, addressing Trac #7436
makeInvmapForType iClass conName tvis covariant (SigT ty _) =
    makeInvmapForType iClass conName tvis covariant ty
makeInvmapForType iClass conName tvis covariant (ForallT tvbs _ ty)
    = makeInvmapForType iClass conName (removeForalled tvbs tvis) covariant ty
makeInvmapForType iClass conName tvis covariant ty =
    let tyCon  :: Type
        tyArgs :: [Type]
        tyCon:tyArgs = unapplyTy ty

        numLastArgs :: Int
        numLastArgs = min (fromEnum iClass) (length tyArgs)

        lhsArgs, rhsArgs :: [Type]
        (lhsArgs, rhsArgs) = splitAt (length tyArgs - numLastArgs) tyArgs

        tyVarNameBases :: [NameBase]
        tyVarNameBases = map fst3 tvis

        doubleMap :: (Bool -> Type -> Q Exp) -> [Type] -> [Q Exp]
        doubleMap _ []     = []
        doubleMap f (t:ts) = f covariant t : f (not covariant) t : doubleMap f ts

        mentionsTyArgs :: Bool
        mentionsTyArgs = any (`mentionsNameBase` tyVarNameBases) tyArgs

        makeInvmapTuple :: Type -> Name -> Q Exp
        makeInvmapTuple fieldTy fieldName =
            appE (makeInvmapForType iClass conName tvis covariant fieldTy) $ varE fieldName

     in case tyCon of
             ArrowT | mentionsTyArgs ->
                 let [argTy, resTy] = tyArgs
                  in [| \x b ->
                         $(makeInvmapForType iClass conName tvis covariant resTy)
                         (x ($(makeInvmapForType iClass conName tvis (not covariant) argTy) b))
                      |]
             TupleT n | n > 0 && mentionsTyArgs -> do
                 x  <- newName "x"
                 xs <- newNameList "x" n
                 lamE [varP x] $ caseE (varE x)
                     [ match (tupP $ map varP xs)
                             (normalB . tupE $ zipWith makeInvmapTuple tyArgs xs)
                             []
                     ]
             _ -> do
                 itf <- isTyFamily tyCon
                 if any (`mentionsNameBase` tyVarNameBases) lhsArgs || (itf && mentionsTyArgs)
                      then outOfPlaceTyVarError conName tyVarNameBases
                      else if any (`mentionsNameBase` tyVarNameBases) rhsArgs
                           then appsE $
                                ( varE (invmapNameTable (toEnum numLastArgs))
                                : doubleMap (makeInvmapForType iClass conName tvis) rhsArgs
                                )
                           else [| \x -> x |] -- See Trac #7436

-------------------------------------------------------------------------------
-- Template Haskell reifying and AST manipulation
-------------------------------------------------------------------------------

-- | Extracts a plain type constructor's information.
withTyCon :: Name -- ^ Name of the plain type constructor
          -> (Cxt -> [TyVarBndr] -> [Con] -> Q a)
          -> Q a
withTyCon name f = do
    info <- reify name
    case info of
        TyConI dec ->
            case dec of
                DataD    ctxt _ tvbs cons _ -> f ctxt tvbs cons
                NewtypeD ctxt _ tvbs con  _ -> f ctxt tvbs [con]
                other -> error $ ns ++ "Unsupported type " ++ show other ++ ". Must be a data type or newtype."
        _ -> error $ ns ++ "The name must be of a plain type constructor."
  where
    ns :: String
    ns = "Data.Functor.Invariant.TH.withTyCon: "

#if MIN_VERSION_template_haskell(2,7,0)
-- | Extracts a data family name's information.
withDataFam :: Name -- ^ Name of the data family
            -> ([TyVarBndr] -> [Dec] -> Q a)
            -> Q a
withDataFam name f = do
    info <- reify name
    case info of
        FamilyI (FamilyD DataFam _ tvbs _) decs -> f tvbs decs
        FamilyI (FamilyD TypeFam _ _    _) _    ->
            error $ ns ++ "Cannot use a type family name."
        other -> error $ ns ++ "Unsupported type " ++ show other ++ ". Must be a data family name."
  where
    ns :: String
    ns = "Data.Functor.Invariant.TH.withDataFam: "

-- | Extracts a data family instance constructor's information.
withDataFamInstCon :: Name -- ^ Name of the data family instance constructor
                   -> ([TyVarBndr] -> Cxt -> Name -> [Type] -> [Con] -> Q a)
                   -> Q a
withDataFamInstCon dficName f = do
    dficInfo <- reify dficName
    case dficInfo of
        DataConI _ _ parentName _ -> do
            parentInfo <- reify parentName
            case parentInfo of
                FamilyI (FamilyD DataFam _ _ _) _ -> withDataFam parentName $ \famTvbs decs ->
                    let sameDefDec = flip find decs $ \dec ->
                          case dec of
                              DataInstD    _ _ _ cons' _ -> any ((dficName ==) . constructorName) cons'
                              NewtypeInstD _ _ _ con   _ -> dficName == constructorName con
                              _ -> error $ ns ++ "Must be a data or newtype instance."

                        (ctxt, instTys, cons) = case sameDefDec of
                              Just (DataInstD    ctxt' _ instTys' cons' _) -> (ctxt', instTys', cons')
                              Just (NewtypeInstD ctxt' _ instTys' con   _) -> (ctxt', instTys', [con])
                              _ -> error $ ns ++ "Could not find data or newtype instance constructor."

                    in f famTvbs ctxt parentName instTys cons
                _ -> error $ ns ++ "Data constructor " ++ show dficName ++ " is not from a data family instance."
        other -> error $ ns ++ "Unsupported type " ++ show other ++ ". Must be a data family instance constructor."
  where
    ns :: String
    ns = "Data.Functor.Invariant.TH.withDataFamInstCon: "
#endif

-- | Deduces the Invariant(2) instance context, instance head, and eta-reduced
-- type variables for a plain data type constructor.
cxtAndTypePlainTy :: InvariantClass -- Invariant or Invariant2
                  -> Name           -- The datatype's name
                  -> Cxt            -- The datatype context
                  -> [TyVarBndr]    -- The type variables
                  -> (Cxt, Type, [NameBase])
cxtAndTypePlainTy iClass tyConName dataCxt tvbs =
    if remainingLength < 0 || not (wellKinded droppedKinds) -- If we have enough well-kinded type variables
       then derivingKindError iClass tyConName
    else if any (`predMentionsNameBase` droppedNbs) dataCxt -- If the last type variable(s) are mentioned in a datatype context
       then datatypeContextError iClass instanceType
    else (instanceCxt, instanceType, droppedNbs)
  where
    instanceCxt :: Cxt
    instanceCxt = map (applyInvariantConstraint)
                $ filter (needsConstraint iClass . tvbKind) remaining

    instanceType :: Type
    instanceType = applyTyCon tyConName $ map (VarT . tvbName) remaining

    remainingLength :: Int
    remainingLength = length tvbs - fromEnum iClass

    remaining, dropped :: [TyVarBndr]
    (remaining, dropped) = splitAt remainingLength tvbs

    droppedKinds :: [Kind]
    droppedKinds = map tvbKind dropped

    droppedNbs :: [NameBase]
    droppedNbs = map (NameBase . tvbName) dropped

#if MIN_VERSION_template_haskell(2,7,0)
-- | Deduces the Invariant(2) instance context, instance head, and eta-reduced
-- type variables for a data family instnce constructor.
cxtAndTypeDataFamInstCon :: InvariantClass -- Invariant or Invariant2
                         -> Name           -- The data family name
                         -> Cxt            -- The datatype context
                         -> [TyVarBndr]    -- The data family declaration's type variables
                         -> [Type]         -- The data family instance types
                         -> (Cxt, Type, [NameBase])
cxtAndTypeDataFamInstCon iClass parentName dataCxt famTvbs instTysAndKinds =
    if remainingLength < 0 || not (wellKinded droppedKinds) -- If we have enough well-kinded type variables
       then derivingKindError iClass parentName
    else if any (`predMentionsNameBase` droppedNbs) dataCxt -- If the last type variable(s) are mentioned in a datatype context
       then datatypeContextError iClass instanceType
    else if canEtaReduce remaining dropped -- If it is safe to drop the type variables
       then (instanceCxt, instanceType, droppedNbs)
    else etaReductionError instanceType
  where
    instanceCxt :: Cxt
    instanceCxt = map (applyInvariantConstraint)
                $ filter (needsConstraint iClass . tvbKind) lhsTvbs

    -- We need to make sure that type variables in the instance head which have
    -- Invariant(2) constraints aren't poly-kinded, e.g.,
    --
    -- @
    -- instance Invariant f => Invariant (Foo (f :: k)) where
    -- @
    --
    -- To do this, we remove every kind ascription (i.e., strip off every 'SigT').
    instanceType :: Type
    instanceType = applyTyCon parentName
                 $ map unSigT remaining

    remainingLength :: Int
    remainingLength = length famTvbs - fromEnum iClass

    remaining, dropped :: [Type]
    (remaining, dropped) = splitAt remainingLength rhsTypes

    droppedKinds :: [Kind]
    droppedKinds = map tvbKind . snd $ splitAt remainingLength famTvbs

    droppedNbs :: [NameBase]
    droppedNbs = map varTToNameBase dropped

    -- We need to be mindful of an old GHC bug which causes kind variables to appear in
    -- @instTysAndKinds@ (as the name suggests) if
    --
    --   (1) @PolyKinds@ is enabled
    --   (2) either GHC 7.6 or 7.8 is being used (for more info, see
    --       https://ghc.haskell.org/trac/ghc/ticket/9692).
    --
    -- Since Template Haskell doesn't seem to have a mechanism for detecting which
    -- language extensions are enabled, we do the next-best thing by counting
    -- the number of distinct kind variables in the data family declaration, and
    -- then dropping that number of entries from @instTysAndKinds@.
    instTypes :: [Type]
    instTypes =
# if __GLASGOW_HASKELL__ >= 710 || !(MIN_VERSION_template_haskell(2,8,0))
        instTysAndKinds
# else
        drop (Set.size . Set.unions $ map (distinctKindVars . tvbKind) famTvbs)
             instTysAndKinds
# endif

    lhsTvbs :: [TyVarBndr]
    lhsTvbs = map (uncurry replaceTyVarName)
            . filter (isTyVar . snd)
            . take remainingLength
            $ zip famTvbs rhsTypes

    -- In GHC 7.8, only the @Type@s up to the rightmost non-eta-reduced type variable
    -- in @instTypes@ are provided (as a result of this extremely annoying bug:
    -- https://ghc.haskell.org/trac/ghc/ticket/9692). This is pretty inconvenient,
    -- as it makes it impossible to come up with the correct Invariant(2)
    -- instances in some cases. For example, consider the following code:
    --
    -- @
    -- data family Foo a b c
    -- data instance Foo Int y z = Foo Int y z
    -- $(deriveInvariant2 'Foo)
    -- @
    --
    -- Due to the aformentioned bug, Template Haskell doesn't tell us the names of
    -- either of type variables in the data instance (@y@ and @z@). As a result, we
    -- won't know which fields of the 'Foo' constructor to apply the map functions,
    -- which will result in an incorrect instance. Urgh.
    --
    -- A workaround is to ensure that you use the exact same type variables, in the
    -- exact same order, in the data family declaration and any data or newtype
    -- instances:
    --
    -- @
    -- data family Foo a b c
    -- data instance Foo Int b c = Foo Int b c
    -- $(deriveInvariant2 'Foo)
    -- @
    --
    -- Thankfully, other versions of GHC don't seem to have this bug.
    rhsTypes :: [Type]
    rhsTypes =
# if __GLASGOW_HASKELL__ >= 708 && __GLASGOW_HASKELL__ < 710
            instTypes ++ map tvbToType
                             (drop (length instTypes)
                                   famTvbs)
# else
            instTypes
# endif
#endif

-- | Given a TyVarBndr, apply an Invariant(2) constraint to it, depending
-- on its kind.
applyInvariantConstraint :: TyVarBndr -> Pred
applyInvariantConstraint (PlainTV  _)         = error "Cannot constrain type of kind *"
applyInvariantConstraint (KindedTV name kind) = applyClass className name
  where
    className :: Name
    className = invariantClassNameTable . toEnum $ numKindArrows kind

-- | Can a kind signature inhabit an Invariant constraint?
--
-- Invariant:  Kind k1 -> k2
-- Invariant2: Kind k1 -> k2 -> k3
needsConstraint :: InvariantClass -> Kind -> Bool
needsConstraint iClass kind =
       fromEnum iClass >= nka
    && nka >= fromEnum Invariant
    && canRealizeKindStarChain kind
  where
   nka :: Int
   nka = numKindArrows kind

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
    className = nameBase $ invariantClassNameTable iClass

-- | One of the last type variables cannot be eta-reduced (see the canEtaReduce
-- function for the criteria it would have to meet).
etaReductionError :: Type -> a
etaReductionError instanceType = error $
    "Cannot eta-reduce to an instance of form \n\tinstance (...) => "
    ++ pprint instanceType

-- | The data type has a DatatypeContext which mentions one of the eta-reduced
-- type variables.
datatypeContextError :: InvariantClass -> Type -> a
datatypeContextError iClass instanceType = error
    . showString "Can't make a derived instance of ‘"
    . showString (pprint instanceType)
    . showString "‘:\n\tData type ‘"
    . showString className
    . showString "‘ must not have a class context involving the last type argument(s)"
    $ ""
  where
    className :: String
    className = nameBase $ invariantClassNameTable iClass

-- | The data type has an existential constraint which mentions one of the
-- eta-reduced type variables.
existentialContextError :: String -> a
existentialContextError conName = error
    . showString "Constructor ‘"
    . showString conName
    . showString "‘ must be truly polymorphic in the last argument(s) of the data type"
    $ ""

-- | The data type mentions one of the n eta-reduced type variables in a place other
-- than the last nth positions of a data type in a constructor's field.
outOfPlaceTyVarError :: String -> [NameBase] -> a
outOfPlaceTyVarError conName tyVarNames = error
    . showString "Constructor ‘"
    . showString conName
    . showString "‘ must use the type variable(s) "
    . showsPrec 0 tyVarNames
    . showString " only in the last argument(s) of a data type"
    $ ""

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

-------------------------------------------------------------------------------
-- Expanding type synonyms
-------------------------------------------------------------------------------

-- | Expands all type synonyms in a type. Written by Dan Rosén in the
-- @genifunctors@ package (licensed under BSD3).
expandSyn :: Type -> Q Type
expandSyn (ForallT tvs ctx t) = fmap (ForallT tvs ctx) $ expandSyn t
expandSyn t@AppT{}            = expandSynApp t []
expandSyn t@ConT{}            = expandSynApp t []
expandSyn (SigT t _)          = expandSyn t   -- Ignore kind synonyms
expandSyn t                   = return t

expandSynApp :: Type -> [Type] -> Q Type
expandSynApp (AppT t1 t2) ts = do
    t2' <- expandSyn t2
    expandSynApp t1 (t2':ts)
expandSynApp (ConT n) ts | nameBase n == "[]" = return $ foldl' AppT ListT ts
expandSynApp t@(ConT n) ts = do
    info <- reify n
    case info of
        TyConI (TySynD _ tvs rhs) ->
            let (ts', ts'') = splitAt (length tvs) ts
                subs = mkSubst tvs ts'
                rhs' = subst subs rhs
             in expandSynApp rhs' ts''
        _ -> return $ foldl' AppT t ts
expandSynApp t ts = do
    t' <- expandSyn t
    return $ foldl' AppT t' ts

type Subst = Map Name Type

mkSubst :: [TyVarBndr] -> [Type] -> Subst
mkSubst vs ts =
   let vs' = map un vs
       un (PlainTV v)    = v
       un (KindedTV v _) = v
   in Map.fromList $ zip vs' ts

subst :: Subst -> Type -> Type
subst subs (ForallT v c t) = ForallT v c $ subst subs t
subst subs t@(VarT n)      = fromMaybe t $ Map.lookup n subs
subst subs (AppT t1 t2)    = AppT (subst subs t1) (subst subs t2)
subst subs (SigT t k)      = SigT (subst subs t) k
subst _ t                  = t

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

invmapConstNameTable :: InvariantClass -> Name
invmapConstNameTable Invariant  = 'invmapConst
invmapConstNameTable Invariant2 = 'invmap2Const

invariantClassNameTable :: InvariantClass -> Name
invariantClassNameTable Invariant  = ''Invariant
invariantClassNameTable Invariant2 = ''Invariant2

invmapNameTable :: InvariantClass -> Name
invmapNameTable Invariant  = 'invmap
invmapNameTable Invariant2 = 'invmap2

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
-- NameBase
-------------------------------------------------------------------------------

-- | A wrapper around Name which only uses the 'nameBase' (not the entire Name)
-- to compare for equality. For example, if you had two Names a_123 and a_456,
-- they are not equal as Names, but they are equal as NameBases.
--
-- This is useful when inspecting type variables, since a type variable in an
-- instance context may have a distinct Name from a type variable within an
-- actual constructor declaration, but we'd want to treat them as the same
-- if they have the same 'nameBase' (since that's what the programmer uses to
-- begin with).
newtype NameBase = NameBase { getName :: Name }

getNameBase :: NameBase -> String
getNameBase = nameBase . getName

instance Eq NameBase where
    (==) = (==) `on` getNameBase

instance Ord NameBase where
    compare = compare `on` getNameBase

instance Show NameBase where
    showsPrec p = showsPrec p . getNameBase

-- | A NameBase paired with the name of its map functions. For example, when deriving
-- Invariant2, its list of TyVarInfos might look like [(a, 'covMap1, 'contraMap1),
-- (b, 'covMap2, 'contraMap2)].
type TyVarInfo = (NameBase, Name, Name)

-------------------------------------------------------------------------------
-- Assorted utilities
-------------------------------------------------------------------------------

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

-- | Extracts the name of a constructor.
constructorName :: Con -> Name
constructorName (NormalC name      _  ) = name
constructorName (RecC    name      _  ) = name
constructorName (InfixC  _    name _  ) = name
constructorName (ForallC _    _    con) = constructorName con

-- | Generate a list of fresh names with a common prefix, and numbered suffixes.
newNameList :: String -> Int -> Q [Name]
newNameList prefix n = mapM (newName . (prefix ++) . show) [1..n]

-- | Remove any occurrences of a forall-ed type variable from a list of @TyVarInfo@s.
removeForalled :: [TyVarBndr] -> [TyVarInfo] -> [TyVarInfo]
removeForalled tvbs = filter (not . foralled tvbs)
  where
    foralled :: [TyVarBndr] -> TyVarInfo -> Bool
    foralled tvbs' tvi = fst3 tvi `elem` map (NameBase . tvbName) tvbs'

-- | Extracts the name from a TyVarBndr.
tvbName :: TyVarBndr -> Name
tvbName (PlainTV  name)   = name
tvbName (KindedTV name _) = name

-- | Extracts the kind from a TyVarBndr.
tvbKind :: TyVarBndr -> Kind
tvbKind (PlainTV  _)   = starK
tvbKind (KindedTV _ k) = k

-- | Replace the Name of a TyVarBndr with one from a Type (if the Type has a Name).
replaceTyVarName :: TyVarBndr -> Type -> TyVarBndr
replaceTyVarName tvb            (SigT t _) = replaceTyVarName tvb t
replaceTyVarName (PlainTV  _)   (VarT n)   = PlainTV  n
replaceTyVarName (KindedTV _ k) (VarT n)   = KindedTV n k
replaceTyVarName tvb            _          = tvb

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
    && allDistinct nbs -- Make sure not to pass something of type [Type], since Type
                       -- didn't have an Ord instance until template-haskell-2.10.0.0
    && not (any (`mentionsNameBase` nbs) remaining)
  where
    nbs :: [NameBase]
    nbs = map varTToNameBase dropped

-- | Extract the Name from a type variable.
varTToName :: Type -> Name
varTToName (VarT n)   = n
varTToName (SigT t _) = varTToName t
varTToName _          = error "Not a type variable!"

-- | Extract the NameBase from a type variable.
varTToNameBase :: Type -> NameBase
varTToNameBase = NameBase . varTToName

-- | Peel off a kind signature from a Type (if it has one).
unSigT :: Type -> Type
unSigT (SigT t _) = t
unSigT t          = t

-- | Is the given type a variable?
isTyVar :: Type -> Bool
isTyVar (VarT _)   = True
isTyVar (SigT t _) = isTyVar t
isTyVar _          = False

-- | Is the given type a type family constructor (and not a data family constructor)?
isTyFamily :: Type -> Q Bool
isTyFamily (ConT n) = do
    info <- reify n
    return $ case info of
#if MIN_VERSION_template_haskell(2,7,0)
         FamilyI (FamilyD TypeFam _ _ _) _ -> True
#else
         TyConI  (FamilyD TypeFam _ _ _)   -> True
#endif
         _ -> False
isTyFamily _ = return False

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

-- | Does the given type mention any of the NameBases in the list?
mentionsNameBase :: Type -> [NameBase] -> Bool
mentionsNameBase = go Set.empty
  where
    go :: Set NameBase -> Type -> [NameBase] -> Bool
    go foralls (ForallT tvbs _ t) nbs =
        go (foralls `Set.union` Set.fromList (map (NameBase . tvbName) tvbs)) t nbs
    go foralls (AppT t1 t2) nbs = go foralls t1 nbs || go foralls t2 nbs
    go foralls (SigT t _)   nbs = go foralls t nbs
    go foralls (VarT n)     nbs = varNb `elem` nbs && not (varNb `Set.member` foralls)
      where
        varNb = NameBase n
    go _       _            _   = False

-- | Does an instance predicate mention any of the NameBases in the list?
predMentionsNameBase :: Pred -> [NameBase] -> Bool
#if MIN_VERSION_template_haskell(2,10,0)
predMentionsNameBase = mentionsNameBase
#else
predMentionsNameBase (ClassP _ tys) nbs = any (`mentionsNameBase` nbs) tys
predMentionsNameBase (EqualP t1 t2) nbs = mentionsNameBase t1 nbs || mentionsNameBase t2 nbs
#endif

-- | The number of arrows that compose the spine of a kind signature
-- (e.g., (* -> *) -> k -> * has two arrows on its spine).
numKindArrows :: Kind -> Int
numKindArrows k = length (uncurryKind k) - 1

-- | Construct a type via curried application.
applyTy :: Type -> [Type] -> Type
applyTy = foldl' AppT

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
unapplyTy :: Type -> [Type]
unapplyTy = reverse . go
  where
    go :: Type -> [Type]
    go (AppT t1 t2) = t2:go t1
    go (SigT t _)   = go t
    go t            = [t]

-- | Split a type signature by the arrows on its spine. For example, this:
--
-- @
-- (Int -> String) -> Char -> ()
-- @
--
-- would split to this:
--
-- @
-- [Int -> String, Char, ()]
-- @
uncurryTy :: Type -> [Type]
uncurryTy (AppT (AppT ArrowT t1) t2) = t1:uncurryTy t2
uncurryTy (SigT t _)                 = uncurryTy t
uncurryTy t                          = [t]

-- | Like uncurryType, except on a kind level.
uncurryKind :: Kind -> [Kind]
#if MIN_VERSION_template_haskell(2,8,0)
uncurryKind = uncurryTy
#else
uncurryKind (ArrowK k1 k2) = k1:uncurryKind k2
uncurryKind k              = [k]
#endif

wellKinded :: [Kind] -> Bool
wellKinded = all canRealizeKindStar

-- | Of form k1 -> k2 -> ... -> kn, where k is either a single kind variable or *.
canRealizeKindStarChain :: Kind -> Bool
canRealizeKindStarChain = all canRealizeKindStar . uncurryKind

canRealizeKindStar :: Kind -> Bool
canRealizeKindStar k = case uncurryKind k of
    [k'] -> case k' of
#if MIN_VERSION_template_haskell(2,8,0)
                 StarT    -> True
                 (VarT _) -> True -- Kind k can be instantiated with *
#else
                 StarK    -> True
#endif
                 _ -> False
    _ -> False

createKindChain :: Int -> Kind
createKindChain = go starK
  where
    go :: Kind -> Int -> Kind
    go k 0 = k
#if MIN_VERSION_template_haskell(2,8,0)
    go k n = go (AppT (AppT ArrowT StarT) k) (n - 1)
#else
    go k n = go (ArrowK StarK k) (n - 1)
#endif

# if MIN_VERSION_template_haskell(2,8,0) && __GLASGOW_HASKELL__ < 710
distinctKindVars :: Kind -> Set Name
distinctKindVars (AppT k1 k2) = distinctKindVars k1 `Set.union` distinctKindVars k2
distinctKindVars (SigT k _)   = distinctKindVars k
distinctKindVars (VarT k)     = Set.singleton k
distinctKindVars _            = Set.empty
#endif

#if __GLASGOW_HASKELL__ >= 708 && __GLASGOW_HASKELL__ < 710
tvbToType :: TyVarBndr -> Type
tvbToType (PlainTV n)    = VarT n
tvbToType (KindedTV n k) = SigT (VarT n) k
#endif
