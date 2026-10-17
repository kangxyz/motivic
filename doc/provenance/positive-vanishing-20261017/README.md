# Positive affine-line vanishing source import (2026-10-17)

This subtree records a fixed source projection from archive SHA-256 `3f5e1eed50f393d1345c753582fd25a4850cf7084befcbca6414a4472fb000c9` onto repository baseline `04569be2fd9324b1911696fb1e67fd90441673c4`. The previous source snapshot is SHA-256 `8e87391f4926200cf6a6b16f22da99bda98948cf2424b5c88aa40b08b9bce670`; its existing provenance index is [../README.md](../README.md). The historical source checkpoint is preserved in [CHECKPOINT.md](CHECKPOINT.md), and the delta-only source/log/hash records are in [SOURCE-INDEX.json](SOURCE-INDEX.json). Three canonical original Linux logs are preserved in [checks/](checks/).

The imported endpoints are in `Motivic.SheafCohomology`. For every field `k`,
every ordinary abelian sheaf `F` on the original big smooth Nisnevich site,
and `n : ℕ`, `affineLine_H_add_two_eq_zero` proves that every element of the
original `H^(n+2)(A¹_k,F)` is zero, retaining the ordinary `HasExt` bookkeeping
and coefficient universe. For a Nisnevich sheaf with transfers whose underlying
presheaf is A¹-invariant, `affineLine_H_succ_eq_zero` proves the corresponding
vanishing in every degree `n+1`. The higher endpoint requires no transfer or
homotopy-invariance premise.

This subtree records source projection and historical compiler evidence. Current independent source review and selected native validation belong to the repository [verification record](../../VERIFICATION.md). The historical checks are not new executions against the projected source bytes. The source does not establish arbitrary small-site coefficient extension, generic-cylinder continuity, or global strict `A¹` invariance. Of the 255 added/changed source paths, 253 have successful historical Linux logs whose source hashes match the archive bytes; two new leaves had no supplied log: `Motivic/Aglib/AlgebraicGeometry/Normalization/FixedFiniteLocusBadIdeal.lean` and `Motivic/Aglib/AlgebraicGeometry/RelativeCurve/AffineRetainedImage.lean`. Historical Linux checks are not current-byte certificates after the authorized author, test namespace, facade import, and terminal namespace projections.

The terminal consumer projection changes its import to the public `Motivic.Cohomology.AffineLine` facade and places its two test theorems and axiom audit in `MotivicTest.SheafCohomologyAffineLineHigherVanishing`; this is recorded explicitly in the source index. Its current native validation is recorded separately in the verification owner.

The two unlogged helpers required proof-encoding corrections.
`AffineRetainedImage` uses explicit affine-open evidence, native relative-dimension
composition and the canonical range-isomorphism factorization.
`FixedFiniteLocusBadIdeal` derives complement membership explicitly before
applying it to a point in the open. Statements, hypotheses, imports and budgets
are unchanged. Both corrected leaves passed capped native compilation. The index
preserves their archive and projected hashes separately from corrected source
hashes; these successful checks are not attributed to nonexistent historical logs.

Final exact-file text/style lint found one trailing space in
`PolynomialQuotientChangeBase`; removing that space changes no declaration or
import. The source index records this additional projection separately.

The integral-localization transcendence-degree helper keeps its explicit domain
hypothesis as part of the quotient-domain API. A documented declaration-local
`unusedArguments` lint exception retains that signature; its proof is unchanged.
This adjustment also has separate projected and current hashes in the index.

[NATIVE-CHECKS.json](NATIVE-CHECKS.json) fixes the selected current source/output
identities and receipt hashes, including explicit conditional-cache and
not-freshly-native-run boundaries.
