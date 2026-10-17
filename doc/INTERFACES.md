# Interface boundaries

The public modules reexport existing constructions. This document records
their intended use and retained hypotheses; it is not an independent proof
review or a theorem-status assignment.

| Interface | Actual objects and retained boundary |
| --- | --- |
| `Motivic.Cor k` | Smooth separated finite-type objects and signed finite correspondences over a field; disconnected and empty objects are included. Composition is the original incidence Tor pairing. |
| `Motivic.PresheafWithTransfers` | Additive contravariant functors on `Cor k`; signed cycle coefficients remain part of the action. |
| `Motivic.SheafWithTransfers` | Additive Nisnevich transfer sheaves and their canonical ordinary graph restriction. The usable sheafification coefficient universe is `u + 1` for a field in `Type u`. |
| `Motivic.SheafCohomology.withTransfers` | Original ordinary Nisnevich cohomology for every `n : ℕ`, arbitrary fields and transfer sheaves. Retains ordinary `HasExt`; constructs transfer-category Ext internally. Graph and coefficient maps are the original maps. |
| `Motivic.Cohomology.AffineLine` | Original ordinary big-smooth Nisnevich `H^(n+2)(A1,F)=0` for arbitrary abelian coefficients; `H^(n+1)=0` for HI sheaves with transfers over any field. Ordinary `HasExt` and coefficient universe `u+1` remain explicit. This does not supply a general small-site comparison or strict invariance on arbitrary smooth schemes. |
| Motivic complexes | Sheafified reduced-torus singular complexes in weight `q`, with singular chain degree `r` in cochain degree `q-r`; differential/shift signs are explicit. |
| Motivic finite coefficients | Derived coefficient construction and the original multiplication/coefficient triangle. A termwise replacement needs its own comparison. |
| Milnor K | Actual integral symbol quotients in every nonnegative degree, independent of the motivic comparison; maps and residues retain their declaration-specific inputs; the optional `Motivic.KTheory.MilnorK.Norms` finite-extension norm tower has characteristic-zero and finite-dimensional hypotheses. |
| Diagonal computation | Original `H^{q,q}` and actual Milnor symbols, with characteristic-zero and derived-category hypotheses retained. |
| Weight one | A quasi-isomorphism to the ordinary Nisnevich unit sheaf shifted by `[-1]`, and the resulting ordinary hypercohomology comparison. No derived-with-transfers replacement is claimed. |

Do not identify arbitrary ordinary sheaves on the `Cor` topology with additive
sheaves with transfers. Sheaf cokernels are genuine sheaf cokernels; section
values need not be objectwise cokernels. Exactness of a forgetful functor alone
does not establish acyclicity: use the actual supplied comparison proofs.

Strict A1 invariance, henselian/essentially-smooth derived continuity, full
canonical purity, positive-characteristic diagonal comparison, and general
higher-Chow/DM/spectrum comparisons retain separate proof obligations. The
[imported roadmap](provenance/strict-a1-proof-roadmap-20261017.md) records the
snapshot frontier. A conditional result, checked theorem family or finite
computation does not close an unsupplied input.
