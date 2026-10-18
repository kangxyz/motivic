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
| `Motivic.Cohomology.A1.GenericDetection` | Over infinite fields, original nonempty-open vanishing for HI presheaves with transfers on smooth integral affine schemes gives actual affine zero-neighborhoods covering all points. No sheaf premise; local-zero conclusion. |
| `Motivic.Cohomology.AffineLine.GenericBase` | Over any field and smooth domain base: classwise eventual higher vanishing for arbitrary ordinary coefficients, plus all-positive vanishing for HI transfer sheaves. Whole line, original maps, coefficient universe and `HasExt` retained; class-dependent open. |
| `Motivic.Cohomology.A1.StrictInvariance` | Every original ordinary Nisnevich cohomology projection is an isomorphism in every natural degree for HI `SheafWithTransfers.{u+1}` coefficients over an infinite perfect field. Retains ordinary `HasExt.{u+1}` and the original groups/maps; no supplied positive-HI or puncture-Mono family. |
| `Motivic.Cohomology.A1.CartierBoundary` | Genuine positive `Rj_*` vanishes for a supplied smooth Cartier complement over an infinite field, assuming current-degree original cohomology HI and the original contraction-to-boundary Epi for every smooth object. Ordinary `HasExt.{u+1}`, coefficients `u+1`, locally rank-one ideal and actual complement equality retained. |
| Motivic complexes | Sheafified reduced-torus singular complexes in weight `q`, with singular chain degree `r` in cochain degree `q-r`; differential/shift signs are explicit. |
| Motivic finite coefficients | Derived coefficient construction and the original multiplication/coefficient triangle. A termwise replacement needs its own comparison. |
| Milnor K | Aglib supplies the actual all-degree symbol quotient `MilnorK.K F n`, products, residues and norms. Its nested `MilnorK.K2`/`K3` tensor presentations are connected by explicit equivalences. The optional `Aglib.KTheory.MilnorK.Norms` tower keeps characteristic-zero, finite-dimensional and scalar-tower hypotheses. Motivic comparison results consume these original groups and maps. |
| Diagonal computation | Original `H^{q,q}` and actual Milnor symbols, with characteristic-zero and derived-category hypotheses retained. |
| Weight one | A quasi-isomorphism to the ordinary Nisnevich unit sheaf shifted by `[-1]`, and the resulting ordinary hypercohomology comparison. No derived-with-transfers replacement is claimed. |

Do not identify arbitrary ordinary sheaves on the `Cor` topology with additive
sheaves with transfers. Sheaf cokernels are genuine sheaf cokernels; section
values need not be objectwise cokernels. Exactness of a forgetful functor alone
does not establish acyclicity: use the actual supplied comparison proofs.

Finite-field strict A1 descent, henselian/essentially-smooth derived continuity, full
canonical purity, positive-characteristic diagonal comparison, and general
higher-Chow/DM/spectrum comparisons retain separate proof obligations. The
[imported roadmap](provenance/strict-a1-proof-roadmap-20261017.md) records the
snapshot frontier. A conditional result, checked theorem family or finite
computation does not close an unsupplied input.

The retained Cartier theorem states its original current-degree HI and boundary
Epi inputs. `Motivic.FiniteEtaleSite.OriginalPresheaf.contractionToBoundary_epi` now supplies
the genuine Epi for HI original presheaves over infinite fields. The strict
invariance theorem supplies higher HI over infinite perfect fields by lower-degree
induction over all HI coefficients, including their actual contractions. Its
puncture-Mono family is constructed rather than assumed. Earlier conditional
rank interfaces retain their exact statements; coefficient-section dense-open
Mono remains a different morphism.
