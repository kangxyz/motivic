# Publication and license scope

On 17 October 2026 the repository owner explicitly authorized public publication
of all code in the supplied motivic milestone source package. Earlier extraction
headers record the permission boundary at extraction time. This publication
authorization supersedes their lack of public-redistribution authorization; it
does not relicense the copied R5 implementations under Apache-2.0. Original
source identities, authorship and license exceptions below remain in force.

The effective Aglib dependency is pinned to
`b11b71d11bf03cf231f0e06b947a7b63d4344a9e`; the older Aglib revision mentioned
below is historical extraction provenance. The project has no R5Lab or Quillen
package dependency. See [snapshot provenance](doc/provenance/README.md).

The source-only Lean import parser in `scripts/library_sources.py` is adapted
from Aglib revision `c9863095f90b8bd312af807dbf0e378df82403b5`, under Apache-2.0.
Development/CI use the shared Aglib build and cache tooling at explicit revisions;
these tooling choices do not change the mathematical dependency pin. Repository
rules are adapted primarily from Aglib, with selected Quillen contribution
conventions. Neither template's unrelated source nor mathematical claims are
adopted by reference.

The following source notice is retained as an extraction record.

# Third-party sources

The current library depends on `kangxyz/aglib` at commit
`40af743ab794d607f566cec0c5417d8e4d02a735`, licensed under Apache-2.0.
Aglib retains its original copyright, authorship and provenance notices.

The former `Motivic/RingTheory/LocalLength` import adapters listed below now
use native Aglib declarations in `Module` and `Module.PrimeFiltrationFrom`.
The finite-algebra fiber and length implementations also live in Aglib.
`FixedSupportMultiplicity` retains its downstream fixed-support statements
under the native namespaces. Their mathematical hypotheses and conclusions
are unchanged. There is no R5Lab or Quillen package dependency.

The following notice documents earlier source snapshots. It does not relicense
those archived copies and does not describe the current seven import adapters.

# Milnor K₂ implementation migration

The seven implementation leaves listed in the historical section below now
live in the independent Aglib package, under `Aglib.KTheory.MilnorK.K2`.
Their former Motivic paths contain import compatibility only. Aglib retains
the original source headers and non-Apache exceptions in its own
`THIRD_PARTY_NOTICES.md`. This relocation supplies one implementation source;
it does not change the original license or publication authorization.

# Historical Milnor K2 source exceptions

`Motivic/KTheory/MilnorK2/Basic.lean`, `Map.lean`, `Symbols.lean`,
`Residue.lean`, `Specialization.lean`, `DVR/Basic.lean`, and
`DVR/Uniformizer.lean` are
minimal local adaptations of the user's original private `kangxyz/r5-lab`
source at commit `1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e`.
Their original source comments and attribution are retained. Adaptation changes
module visibility, import paths and the local namespace; exact mathematical
statements and proofs are retained except documented compilation fixes.
These copied implementations have no declared upstream license and are
excluded from this project's Apache-2.0 statement. This source reuse supplies
no authorization for public redistribution. Independently authored consumers
and motivic comparison adapters retain their own explicit license headers.

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

The exact source URLs are retained in each file header. These leaves depend on
mathlib and each other only, with no R5Lab package, Grayson or Quillen import.
They construct the standard degree-two tensor/Steinberg quotient and its
symbol and field-map interfaces, and degree-two residue/specialization
under their explicit valuation and reduction hypotheses, with realization
from actual DVR/fraction-field instances and uniformizer change; they do not supply a canonical finite Milnor
norm, reciprocity, or a motivic comparison isomorphism.

# Historical extracted-source provenance

The seven files listed below are adapted from the private user-owned `kangxyz/r5-lab` repository, commit `d20d60bd641037043e5d65ca817332db56f89e7e`. Local extraction was authorized within the user's request to reuse existing local-length calculations. This is not permission to publish the older source or a representation that it has an open-source license.

The source snapshot contains no declared license. These seven extracted files are excluded from the standalone project's Apache-2.0 license statement. Their original source attribution and comments are preserved; the exact upstream paths and Git blob identities follow. Independently authored files, including `KoszulPair.lean`, retain their own explicit Apache-2.0 headers.

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

Adaptations: file paths and namespace changed from `R5Lab.RingTheory.LocalLength` to the standalone `Motivic` ownership; Lean module/public section declarations added; imported modules made explicit public imports; the source's global 1,000,000-heartbeat settings removed. Each leaf is checked using the library's standard 200,000-heartbeat driver. Further compatibility adaptations use plain local instance declarations instead of `letI`/`haveI`, update deprecated conditional-rewrite names, and remove unused or unnecessary simplifier arguments. No mathematical hypotheses or conclusions were changed. The extraction report records verification and any local budget exception. No R5Lab application, Grayson package, or arithmetic comparison module is imported.
