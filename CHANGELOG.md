# next
* Added `Data.Functor.Invariant.Generic` module, which exports a
  `genericInvmap` function on GHC 7.2 or later
* Make `Proxy` and `Tagged` instances poly-kinded

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
