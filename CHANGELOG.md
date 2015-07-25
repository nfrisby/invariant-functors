# next
* Support deriving `Invariant` and `Invariant2` instances with Template Haskell
* Added `invmapFunctor`, `invmapContravariant`, `invmap2Bifunctor`, and
  `invmap2Profunctor` to make defining `Invmap` and `Invmap2` instances
  somewhat easier
* Added `WrappedFunctor`, `WrappedContravariant`, `WrappedBifunctor`, and
  `WrappedProfunctor` data types to allow use of `invmap` and `invmap2` for
  data types that aren't `Invariant` or `Invariant2` instances.
* Added `Invariant` and `Invariant2` instances for data types in the
  `bifunctors` and `profunctors` libraries

# 0.1.2
* Add `Invariant` instances for `Dual` and `Endo`

# 0.1.1
* Bump `contravariant` upper version bounds

# 0.1.0
* Initial commit
