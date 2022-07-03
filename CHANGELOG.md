# 0.6 [2022.07.03]
* Loosen the `Monad` constraint in the `Invariant(2)` instances for
  `Kleisli` to an `Invariant` constraint.
* Loosen the `Comonad` constraint in the `Invariant2` instance for `Cokleisli`
  to an `Invariant` constraint.
* Add `Invariant` instances for `PastroSum`, `CopastroSum`, `Environment`,
  `FreeMapping`, `Pastro`, and `FreeTraversing` from the `profunctors` library.
* Add `Invariant(2)` instances for `Copastro` and `Coyoneda` from the
  `profunctors` library.

# 0.5.6 [2022.05.07]
* Add `InvariantProfunctor` and `InvariantArrow` newtypes that admit
  implementations of `invmap` that only require `Profunctor` or `Arrow`
  constraints, respectively. Also add top-level `invmapProfunctor` and
  `invmapArrow` functions.

# 0.5.5 [2021.11.01]
* Allow building with GHC 9.2.
* Allow building with `transformers-0.6.*`.

# 0.5.4 [2020.10.01]
* Fix a bug in which `deriveInvariant2` would fail on certain data types with
  three or parameters if the first two parameters had phantom roles.
* Fix a bug in which `deriveInvariant(2)` would fail on sufficiently complex
  uses of rank-n types in constructor fields.
* Fix a bug in which `deriveInvariant(2)` would needlessly reject data types
  whose two last type parameters appear as oversaturated arguments to a type
  family.

# 0.5.3 [2019.05.02]
* Implement `foldMap'` in the `Foldable` instance for `WrappedFunctor` when
  building with `base-4.13` or later.

# 0.5.2 [2019.04.26]
* Support `th-abstraction-0.3.0.0` or later.
* Only incur a `semigroups` dependency on old GHCs.

# 0.5.1 [2018.07.15]
* Depend on `QuickCheck-2.11` or later in the test suite.
* Some Haddock fixes in `Data.Functor.Invariant.TH`.

# 0.5 [2017.12.07]
* `Data.Functor.Invariant.TH` now derives `invmap(2)` implementations for empty
  data types that are strict in the argument.
* When using `Data.Functor.Invariant.TH` to derive `Invariant(2)` instances for
  data types where the last type variables are at phantom roles, generated
  `invmap(2)` implementations now use `coerce` for efficiency.
* Add `Options` to `Data.Functor.Invariant.TH`, along with variants of existing
  functions that take `Options` as an argument. For now, the only configurable
  option is whether derived instances for empty data types should use the
  `EmptyCase` extension (this is disabled by default).

# 0.4.3 [2017.07.31]
* Add `Invariant(2)` instances for `Data.Profunctor.Yoneda.Yoneda`.

# 0.4.2 [2017.04.24]
* `invariant.cabal` used to incorrectly state the license was BSD3 when it was
  in fact BSD2. This is now fixed.

# 0.4.1
* Fix the `Invariant V1` instance so as to `seq` its argument
* Allow building with `template-haskell-2.12`

# 0.4
* Allow TH derivation of `Invariant(2)` instances for datatypes containing
  unboxed tuple types
* Ensure `Invariant(2)` instances are in-scope when importing
  `Data.Functor.Invariant`
* Add `Invariant` and `Invariant2` instances for `Kleisli` and `Cokleisli`
* Add `Category` and `Arrow`-like instances for `WrappedProfunctor`

# 0.3.1
* Rewrote `Data.Functor.Invariant.TH`'s type inferencer. This avoids a nasty
  GHC 7.8-specific bug involving derived `Invariant(2)` instances for data
  families.
* Add `Invariant` instances for `Data.Complex.Complex`, `Data.Monoid.Product`,
  and `Data.Monoid.Sum`

# 0.3
* Require `bifunctors-5.2` and `profunctors-5.2`. Add `Invariant(2)` instances
  for newly introduced datatypes from those packages.
* Add `ProfunctorFunctor`, `ProfunctorMonad`, `ProfunctorComonad`, `Mapping`,
  and `Traversing` instances for `WrappedProfunctor`
* Add `StateVar` as a dependency. Add `Invariant` instances for `StateVar` and
  `SettableStateVar`.
* Add `Invariant` instances for `URec` (added to `GHC.Generics` in
  `base-4.9.0.0`)

# 0.2.2
* Add `genericInvmap` function (and make it the default implementation of
  `invmap` for `Invariant` instances) on GHC 7.2 or later
* Make `Tagged` instance poly-kinded

# 0.2.1
* Add `Foldable` and `Traversable` instances for `WrappedFunctor`
* Fixed build on GHC HEAD

# 0.2
* Support deriving `Invariant` and `Invariant2` instances with Template Haskell
* Added `invmapFunctor`, `invmapContravariant`, `invmap2Bifunctor`, and
  `invmap2Profunctor` to make defining `Invmap` and `Invmap2` instances
  somewhat easier
* Added `WrappedFunctor`, `WrappedContravariant`, `WrappedBifunctor`, and
  `WrappedProfunctor` data types to allow use of `invmap` and `invmap2` for
  data types that aren't `Invariant` or `Invariant2` instances.
* Added `Invariant` instances for lazy `ST`, `ArrowMonad`, `Handler`,
  `Identity`, `First`, `Last`, `Alt`, `Proxy`, `ArgDescr`, `ArgOrder`, and
  `OptDescr`
* Added `Invariant` and `Invariant2` instances for data types in the `array`,
  `bifunctors`, `containers`, `profunctors`, `semigroups`, `stm`, `tagged`,
  `transformers`, and `unordered-containers` libraries

# 0.1.2
* Add `Invariant` instances for `Dual` and `Endo`

# 0.1.1
* Bump `contravariant` upper version bounds

# 0.1.0
* Initial commit
