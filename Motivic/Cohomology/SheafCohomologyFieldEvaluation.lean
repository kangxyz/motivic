/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomology
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Ordinary Nisnevich cohomology at the actual base field

The free abelian sheaf representing sections at the base object of the smooth
Nisnevich site over an arbitrary field is projective: epimorphisms of sheaves
are surjective on those sections by the existing split-cover theorem.
Consequently the actual ordinary Ext cohomology vanishes in positive degrees
for every ordinary abelian coefficient sheaf. The Ext universe is independent
of the original coefficient universe.

These statements evaluate at the actual base object `Spec k` on its own smooth
site. They do not compute its affine-line cylinder or a general henselian stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Motivic.Hypercohomology

/-- The actual free section-representing sheaf of the smooth base field is projective. -/
theorem projective_freeAbelianSheaf_base (k : Type u) [Field k] :
    Projective (freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k)))) :=
  projective_freeAbelianSheaf _ _ (fun φ ↦ SmoothSite.surjective_app_base_of_epi k φ)

end Motivic.Hypercohomology

namespace Motivic.SheafCohomology

variable (k : Type u) [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})

/-- Every positive-degree class of the actual ordinary cohomology of the base field vanishes. -/
theorem H_succ_base_eq_zero (n : ℕ)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k))) F
      (n + 1) (SmoothSite.base (Spec (.of k)))) : x = 0 := by
  let := Hypercohomology.projective_freeAbelianSheaf_base k
  change Ext (Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k))))
    F (n + 1) at x
  exact Ext.eq_zero_of_projective x

/-- The actual positive-degree ordinary cohomology group at the base field is a subsingleton. -/
theorem subsingleton_H_succ_base (n : ℕ) :
    Subsingleton (H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 1)
      (SmoothSite.base (Spec (.of k)))) :=
  subsingleton_of_forall_eq 0 (H_succ_base_eq_zero k F n)

/-- Positive-degree ordinary cohomology at the actual base field is a zero group object. -/
theorem isZero_H_succ_base (n : ℕ) :
    IsZero (H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k))) F
      (n + 1) (SmoothSite.base (Spec (.of k)))) := by
  let := subsingleton_H_succ_base k F n
  exact AddCommGrpCat.isZero_of_subsingleton _

end Motivic.SheafCohomology
