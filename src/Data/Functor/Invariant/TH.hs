{-# LANGUAGE CPP #-}

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

import           Data.Functor.Invariant.TH.Internal
import           Data.List
#if __GLASGOW_HASKELL__ < 710 && MIN_VERSION_template_haskell(2,8,0)
import qualified Data.Set as Set
#endif

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

* In GHC 7.8, a bug exists that can cause problems when a data family declaration and
  one of its data instances use different type variables, e.g.,

  @
  data family Foo a b c
  data instance Foo Int y z = Foo Int y z
  $('deriveInvariant' 'Foo)
  @

  To avoid this issue, it is recommened that you use the same type variables in the
  same positions in which they appeared in the data family declaration:

  @
  data family Foo a b c
  data instance Foo Int b c = Foo Int b c
  $('deriveInvariant' 'Foo)
  @

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
    fromCons name' ctxt tvbs cons mbTys = (:[]) `fmap`
        instanceD (return instanceCxt)
                  (return instanceType)
                  (invmapDecs droppedNbs cons)
      where
        (instanceCxt, instanceType, droppedNbs) =
            buildTypeInstance iClass name' ctxt tvbs mbTys

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
    classFuncName = invmapName . toEnum $ length nbs

-- | Generates a lambda expression which behaves like invmap (for Invariant),
-- or invmap2 (for Invariant2).
makeInvmapClass :: InvariantClass -> Name -> Q Exp
makeInvmapClass iClass name = withType name fromCons
  where
    fromCons :: Name -> Cxt -> [TyVarBndr] -> [Con] -> Maybe [Type] -> Q Exp
    fromCons name' ctxt tvbs cons mbTys =
        let nbs = thd3 $ buildTypeInstance iClass name' ctxt tvbs mbTys
         in nbs `seq` makeInvmapForCons nbs cons

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
        $ [ varE $ invmapConstName iClass
          , if null cons
               then appE (varE errorValName)
                         (stringE $ "Void " ++ nameBase (invmapName iClass))
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
       then existentialContextError $ constructorName con
       else makeInvmapForCon iClass (removeForalled tvbs tvis) con

makeInvmapForArgs :: InvariantClass
                  -> [TyVarInfo]
                  -> Name
                  -> [Type]
                  -> [Name]
                  ->  Q Match
makeInvmapForArgs iClass tvis conName tys args =
    let mappedArgs :: [Q Exp]
        mappedArgs = zipWith (makeInvmapForArg iClass conName tvis) tys args
     in match (conP conName $ map varP args)
              (normalB . appsE $ conE conName:mappedArgs)
              []

-- | Generates a lambda expression for invmap(2) for an argument of a constructor.
makeInvmapForArg :: InvariantClass
                 -> Name
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
                  -> Name
                  -> [TyVarInfo]
                  -> Type
                  -> Name
                  -> Q Exp
makeInvmapForArg' iClass conName tvis ty tyExpName =
    appE (makeInvmapForType iClass conName tvis True ty) (varE tyExpName)

-- | Generates a lambda expression for invmap(2) for a specific type.
-- The generated expression depends on the number of type variables.
makeInvmapForType :: InvariantClass
                  -> Name
                  -> [TyVarInfo]
                  -> Bool
                  -> Type
                  -> Q Exp
makeInvmapForType _ _ tvis covariant (VarT tyName) =
    case lookup2 (NameBase tyName) tvis of
         Just (covMap, contraMap) ->
             varE $ if covariant then covMap else contraMap
         Nothing -> do -- Produce a lambda expression rather than id, addressing Trac #7436
             x <- newName "x"
             lamE [varP x] $ varE x
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
                  in do x <- newName "x"
                        b <- newName "b"
                        lamE [varP x, varP b] $
                          makeInvmapForType iClass conName tvis covariant resTy `appE` (varE x `appE`
                            (makeInvmapForType iClass conName tvis (not covariant) argTy `appE` varE b))
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
                                ( varE (invmapName (toEnum numLastArgs))
                                : doubleMap (makeInvmapForType iClass conName tvis) rhsArgs
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
        DataD    ctxt _ tvbs cons _ -> f name ctxt tvbs cons Nothing
        NewtypeD ctxt _ tvbs con  _ -> f name ctxt tvbs [con] Nothing
        _ -> error $ ns ++ "Unsupported type: " ++ show dec
#if MIN_VERSION_template_haskell(2,7,0)
# if __GLASGOW_HASKELL__ >= 711
    DataConI _ _ parentName   -> do
# else
    DataConI _ _ parentName _ -> do
# endif
      parentInfo <- reify parentName
      case parentInfo of
        FamilyI (FamilyD DataFam _ tvbs _) decs ->
          let instDec = flip find decs $ \dec -> case dec of
                DataInstD    _ _ _ cons _ -> any ((name ==) . constructorName) cons
                NewtypeInstD _ _ _ con  _ -> name == constructorName con
                _ -> error $ ns ++ "Must be a data or newtype instance."
           in case instDec of
                Just (DataInstD    ctxt _ instTys cons _)
                  -> f parentName ctxt tvbs cons $ Just instTys
                Just (NewtypeInstD ctxt _ instTys con  _)
                  -> f parentName ctxt tvbs [con] $ Just instTys
                _ -> error $ ns ++
                  "Could not find data or newtype instance constructor."
        _ -> error $ ns ++ "Data constructor " ++ show name ++
          " is not from a data family instance constructor."
    FamilyI (FamilyD DataFam _ _ _) _ -> error $ ns ++
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

-- | Deduces the instance context, instance head, and eta-reduced type variables
-- for an instance.
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
                  -> (Cxt, Type, [NameBase])
-- Plain data type/newtype case
buildTypeInstance iClass tyConName dataCxt tvbs Nothing =
    if remainingLength < 0 || not (wellKinded droppedKinds) -- If we have enough well-kinded type variables
       then derivingKindError iClass tyConName
    else if any (`predMentionsNameBase` droppedNbs) dataCxt -- If the last type variable(s) are mentioned in a datatype context
       then datatypeContextError tyConName instanceType
    else (instanceCxt, instanceType, droppedNbs)
  where
    instanceCxt :: Cxt
    instanceCxt = map (applyInvariantConstraint)
                $ filter (needsConstraint iClass . tvbKind) remaining

    instanceType :: Type
    instanceType = AppT (ConT $ invariantClassName iClass)
                 . applyTyCon tyConName
                 $ map (VarT . tvbName) remaining

    remainingLength :: Int
    remainingLength = length tvbs - fromEnum iClass

    remaining, dropped :: [TyVarBndr]
    (remaining, dropped) = splitAt remainingLength tvbs

    droppedKinds :: [Kind]
    droppedKinds = map tvbKind dropped

    droppedNbs :: [NameBase]
    droppedNbs = map (NameBase . tvbName) dropped
-- Data family instance case
buildTypeInstance iClass parentName dataCxt tvbs (Just instTysAndKinds) =
    if remainingLength < 0 || not (wellKinded droppedKinds) -- If we have enough well-kinded type variables
       then derivingKindError iClass parentName
    else if any (`predMentionsNameBase` droppedNbs) dataCxt -- If the last type variable(s) are mentioned in a datatype context
       then datatypeContextError parentName instanceType
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
    instanceType = AppT (ConT $ invariantClassName iClass)
                 . applyTyCon parentName
                 $ map unSigT remaining

    remainingLength :: Int
    remainingLength = length tvbs - fromEnum iClass

    remaining, dropped :: [Type]
    (remaining, dropped) = splitAt remainingLength rhsTypes

    droppedKinds :: [Kind]
    droppedKinds = map tvbKind . snd $ splitAt remainingLength tvbs

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
#if __GLASGOW_HASKELL__ >= 710 || !(MIN_VERSION_template_haskell(2,8,0))
        instTysAndKinds
#else
        drop (Set.size . Set.unions $ map (distinctKindVars . tvbKind) tvbs)
             instTysAndKinds
#endif

    lhsTvbs :: [TyVarBndr]
    lhsTvbs = map (uncurry replaceTyVarName)
            . filter (isTyVar . snd)
            . take remainingLength
            $ zip tvbs rhsTypes

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
#if __GLASGOW_HASKELL__ >= 708 && __GLASGOW_HASKELL__ < 710
            instTypes ++ map tvbToType
                             (drop (length instTypes)
                                   tvbs)
#else
            instTypes
#endif

-- | Given a TyVarBndr, apply an Invariant(2) constraint to it, depending
-- on its kind.
applyInvariantConstraint :: TyVarBndr -> Pred
applyInvariantConstraint (PlainTV  _)         = error "Cannot constrain type of kind *"
applyInvariantConstraint (KindedTV name kind) = applyClass className name
  where
    className :: Name
    className = invariantClassName . toEnum $ numKindArrows kind

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
outOfPlaceTyVarError :: Name -> [NameBase] -> a
outOfPlaceTyVarError conName tyVarNames = error
    . showString "Constructor ‘"
    . showString (nameBase conName)
    . showString "‘ must use the type variable(s) "
    . showsPrec 0 tyVarNames
    . showString " only in the last argument(s) of a data type"
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
