# Early source migrations

These identities record earlier versions maintained in `kangxyz/r5-lab`
before the standalone libraries. The current code is released under the
repository's Apache-2.0 license. Historical extraction notices are preserved
only in the original imported snapshot.

## Degree-two Milnor theory

Original revision: `1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`.
The implementations now live under `Aglib.KTheory.MilnorK.K2`; the original
Motivic module paths are import adapters. Earlier source paths and hashes follow.

- Basic: original path `lean/R5Lab/KTheory/MilnorK2/Basic.lean`,
  Git blob `50f041a15e0cfb0272fb20a84a30a22ff236e951`,
  SHA-256 `fe9037363f78ceaa75e33db45394bb76deae47cd9118d98d53050f7b40f2f331`.
- Map: original path `lean/R5Lab/KTheory/MilnorK2/Map.lean`,
  Git blob `0ed0027775b5dbbda46704dc538fc11d8c3c873e`,
  SHA-256 `b1608cf9735d2c0e28a0ddefec3c599684d5fc8116d8c3a9559f54a415f0637b`.
- Symbols: original path `lean/R5Lab/KTheory/MilnorK2/Symbols.lean`,
  Git blob `e4d139520b5bdd10bbe4cab79c5ee71b97f2d945`,
  SHA-256 `cbce55a1358e59c4a0ef965dd90603023069b5674692ce98017096d7c22b408c`.

- Residue: original path `lean/R5Lab/KTheory/MilnorK2/Residue.lean`,
  Git blob `e7b6f75478320a087e11e7476e06ab96387fcc3f`,
  SHA-256 `6ff41c485e14afbe170e6c00507e3fd7600bb70851b09c1b8b8245faae048244`.
- Specialization: original path `lean/R5Lab/KTheory/MilnorK2/Specialization.lean`,
  Git blob `be5a8039ea5680958df9dcdad03708dc47375cfb`,
  SHA-256 `af983c26e1abf33e7d04a8a1e80f83365f0025a2aea6d2bd6e1047d13cd12763`.

- DVR/Basic: original path `lean/R5Lab/KTheory/MilnorK2/DVR/Basic.lean`,
  Git blob `982954b1c6d9be98609a0ef7178504641447f1a3`,
  SHA-256 `c6d8cb601ec3a3a3e0beee5ae790e2014aba991545db33e8a125812b33312f37`.
- DVR/Uniformizer: original path `lean/R5Lab/KTheory/MilnorK2/DVR/Uniformizer.lean`,
  Git blob `e67b46fca44619f52849f94eb2f671747b6a46ec`,
  SHA-256 `2afdfc3041049ea4ef56d419e8483e122b14982fd4ca6ec1220bb12ca9c567c9`.

## Local length and principal Euler theory

Original revision: `d20d60bd641037043e5d65ca817332db56f89e7e`.
Implementations now have native Aglib owners; Motivic retains compatibility
imports and downstream geometric statements.

- PrimeFiltration.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrimeFiltration.lean
  - Git blob: `a10feb980d4d35b145c01207abb77fcc22a7e723`
  - Direct upstream imports: `Mathlib.RingTheory.Ideal.AssociatedPrime.Basic`, `Mathlib.LinearAlgebra.Isomorphisms`
- PrincipalEuler.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrincipalEuler.lean
  - Git blob: `4124206999d6b15b42bf2291cae2a48e306fe8fe`
  - Direct upstream imports: `Mathlib.RingTheory.Length`, `Mathlib.LinearAlgebra.Isomorphisms`, `Mathlib.LinearAlgebra.TensorProduct.RightExactness`
- PrincipalEulerAdditivity.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrincipalEulerAdditivity.lean
  - Git blob: `11a53cfdfa626ca0aaa57e1f475c3e218b536be0`
  - Direct upstream imports: `R5Lab.RingTheory.LocalLength.PrincipalEuler`, `Mathlib.Algebra.Module.SnakeLemma`, `Mathlib.Algebra.BigOperators.Fin`
- PrincipalEulerFiltration.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrincipalEulerFiltration.lean
  - Git blob: `fda966c8e691c73941713a9f2986f09999139af4`
  - Direct upstream imports: `R5Lab.RingTheory.LocalLength.PrincipalEulerAdditivity`, `R5Lab.RingTheory.LocalLength.PrimeFiltration`
- PrincipalEulerSupport.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrincipalEulerSupport.lean
  - Git blob: `9782703533447f8178dd920b808d49fea23477d8`
  - Direct upstream imports: `R5Lab.RingTheory.LocalLength.PrincipalEulerFiltration`, `Mathlib.RingTheory.Support`, `Mathlib.RingTheory.LocalRing.Basic`
- PrimeFiltrationMultiplicity.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrimeFiltrationMultiplicity.lean
  - Git blob: `ee57eb65e151194ade11a584a4c129c7e9e41d5b`
  - Direct upstream imports: `R5Lab.RingTheory.LocalLength.PrincipalEulerSupport`, `Mathlib.RingTheory.Flat.Basic`, `Mathlib.RingTheory.Flat.Localization`, `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`
- PrincipalEulerAssociativity.lean
  - Upstream: https://github.com/kangxyz/r5-lab/blob/d20d60bd641037043e5d65ca817332db56f89e7e/lean/R5Lab/RingTheory/LocalLength/PrincipalEulerAssociativity.lean
  - Git blob: `d4a6d37c861eca98fb316d6edc5ee3327c4c3f03`
  - Direct upstream imports: `R5Lab.RingTheory.LocalLength.PrimeFiltrationMultiplicity`, `Mathlib.RingTheory.KrullDimension.Regular`, `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`
