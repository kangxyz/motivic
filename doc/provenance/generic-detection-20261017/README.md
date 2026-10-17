# Generic detection and relative-line source import (2026-10-17)

This source projection records archive SHA-256 `972401892b0b3753d3b3538cdfdb37a6b9ac72991b5c176dfd78219b249267c7` against repository baseline `04dba9fcfe14ac83ec2a5ef70e533ccc50a01de5`; the prior raw archive is `3f5e1eed50f393d1345c753582fd25a4850cf7084befcbca6414a4472fb000c9`. See [../README.md](../README.md) for the earlier provenance snapshot, [CHECKPOINT.md](CHECKPOINT.md) for the preserved historical checkpoint record, and [SOURCE-INDEX.json](SOURCE-INDEX.json) for all 181 delta source identities, transforms, hashes, and evidence status. Four canonical source/test logs for the two primary targets are preserved under [checks/](checks/).

The admitted generic-detection endpoint is the source statement in `Motivic.PresheafWithTransfers`: over an infinite field and smooth commutative domain algebra, for an original smooth-site object with a nonempty actual open immersion into `Spec B`, an A¹-invariant presheaf with transfers section that restricts to zero on that open has an affine original zero-neighborhood at each point; all such zero-neighborhood opens have supremum top. The source requires no sheaf premise on the presheaf. Finite fields, general nonintegral smooth objects, and the final contraction/generic-detection assembly remain outside this endpoint.

The admitted relative-line endpoint states that for any field `k`, smooth commutative domain `R/k`, arbitrary ordinary abelian sheaf `F` on the original big-smooth Nisnevich site with original `HasExt`, and `n : Nat`, a class in original `H^(n+2)(A¹_R,F)` becomes zero after two nonzero `Away` base localizations and an affine base open containing the generic point, under the literal original restriction. The statement adds no HI premise and asserts no field-replacement cohomology or small-site extension. The unlogged relative generic H¹/positive-degree files and their test are archived as source bytes only; they are not admitted or claimed as proved.

Of 181 delta source files, 175 have successful supplied Linux logs with matching incoming-source SHA-256; six unlogged leaves are preserved byte-for-byte in `unverified-source/` and are marked not executed. No proof-failure conclusion follows from missing logs. The two changed helpers retain the current repository proofs and their separate previous native evidence; incoming Linux logs describe only the raw incoming bytes. Prior whitespace/no-lint repairs in `PolynomialQuotientChangeBase.lean` and `PolynomialQuotientFractionTrdeg.lean` remain untouched. This delivery is source projection and provenance, not a new mathematical review or native check.

The two terminal tests use the public facades `Motivic.Cohomology.A1.GenericDetection` and `Motivic.Cohomology.AffineLine.GenericBase`. The relative-line test body is namespaced as `MotivicTest.SheafCohomologyRelativeLineHigherVanishing`; the generic-detection test keeps its native mathematical namespace and examples.
Current independent review and focused native checks are recorded in the
[verification owner](../../VERIFICATION.md). The original generic-detection
result asserts local zero on a covering family; it does not infer global zero
for an arbitrary presheaf. The relative-line open may depend on the class.

[CHECKS.json](CHECKS.json) records the three Mathlib-only native leaf checks,
15 declaration linters per selected module, final exact-file text/style coverage
and source/CI selection checks. A single trailing space in
`WholeAffineLineH1Correction` was removed and rechecked separately; the index
preserves its projected and current source identities.
[CI-CACHE-CHECK.json](CI-CACHE-CHECK.json) is a timed observation of the previous
`04dba9f` run and cache use, not a claim about this new merge's future CI result.
