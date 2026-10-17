/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyFieldEvaluation
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichHenselianEvaluation

/-!
# Ordinary cohomology at actual smooth henselian spectra

An actual smooth separated quasi-compact structure map from a henselian local
spectrum defines an object of the smooth Nisnevich site. The existing free
section-representing sheaf of that object is projective, and its actual ordinary
Ext cohomology with any coefficient sheaf vanishes in positive degrees.

The Ext universe remains independent. This is a statement about actual objects
of the smooth site, with the structure-map hypotheses explicit, rather than a
stalk comparison or an assertion about arbitrary henselizations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Motivic.Hypercohomology

/-- The actual free section-representing sheaf of a smooth henselian spectrum is projective. -/
theorem projective_freeAbelianSheaf_of_henselian {S : Scheme.{u}}
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (p : Spec (.of R) ⟶ S) [Smooth p] [IsSeparated p] [QuasiCompact p] :
    Projective (freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology S) (SmoothSite.mk p)) :=
  projective_freeAbelianSheaf _ _
    (fun φ ↦ SmoothSite.surjective_app_of_epi_of_henselian R p φ)

end Motivic.Hypercohomology

namespace Motivic.SheafCohomology

variable {S : Scheme.{u}} (R : Type u) [CommRing R] [HenselianLocalRing R]
  (p : Spec (.of R) ⟶ S) [Smooth p] [IsSeparated p] [QuasiCompact p]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})

/-- Every positive-degree ordinary cohomology class at this actual henselian object vanishes. -/
theorem H_succ_eq_zero_of_henselian (n : ℕ)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F
      (n + 1) (SmoothSite.mk p)) : x = 0 := by
  let := Hypercohomology.projective_freeAbelianSheaf_of_henselian R p
  change Ext (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology S) (SmoothSite.mk p)) F (n + 1) at x
  exact Ext.eq_zero_of_projective x

/-- Positive-degree ordinary cohomology at the actual henselian object is a subsingleton. -/
theorem subsingleton_H_succ_of_henselian (n : ℕ) :
    Subsingleton (H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F
      (n + 1) (SmoothSite.mk p)) :=
  subsingleton_of_forall_eq 0 (H_succ_eq_zero_of_henselian R p F n)

/-- Positive-degree ordinary cohomology at the actual henselian object is a zero group object. -/
theorem isZero_H_succ_of_henselian (n : ℕ) :
    IsZero (H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology S) F
      (n + 1) (SmoothSite.mk p)) := by
  let := subsingleton_H_succ_of_henselian R p F n
  exact AddCommGrpCat.isZero_of_subsingleton _

end Motivic.SheafCohomology
