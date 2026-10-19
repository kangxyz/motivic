/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.HenselianEvaluation
public import Motivic.Transfers.Sheaf.Basic

/-!
# Actual smooth henselian objects and their ordinary Ext cohomology

The consumers keep all structure-map hypotheses explicit, extract a literal
smooth-site section of a covering member, and use standard Ext from the actual
free abelian sheaf. The field specialization evaluates the original ordinary
cohomology of a transfer sheaf at the actual base object.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.Cohomology.SheafCohomologyHenselianEvaluation

section Henselian

variable {S : Scheme.{u}} (R : Type u) [CommRing R] [HenselianLocalRing R]
  (p : Spec (.of R) ⟶ S) [Smooth p] [IsSeparated p] [QuasiCompact p]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- The splitting lives in the actual smooth site, and not only among underlying schemes. -/
theorem actual_cover_member_splits {P : Presieve (SmoothSite.mk p)}
    (hP : P ∈ SmoothSite.nisnevichPrecoverage S _) :
    ∃ (Y : SmoothSite S) (f : Y ⟶ SmoothSite.mk p),
      P f ∧ ∃ t : SmoothSite.mk p ⟶ Y, t ≫ f = 𝟙 _ :=
  SmoothSite.exists_section_of_mem_nisnevichPrecoverage_of_henselian R p hP

/-- Literal standard-Ext classes vanish for arbitrary coefficients and actual structure maps. -/
theorem actual_henselian_ext_succ_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Ext.{u + 2} (_root_.CategoryTheory.Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology S) (SmoothSite.mk p)) F (n + 1)) : x = 0 :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.H_succ_eq_zero_of_henselian R p F n x

end Henselian

section Field

variable (k : Type u) [Field k]

local instance : HasExt.{u + 2}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :=
  HasExt.standard _

/-- The henselian theorem specializes to the field base and original transfer coefficients. -/
theorem original_transfer_field_base_isZero (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    IsZero (_root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf.{u + 1} k).obj F) (n + 1)
      (SmoothSite.base (Spec (.of k)))) :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.isZero_H_succ_of_henselian k (𝟙 _) _ n

/-- The separately proved field endpoint computes the same original ordinary cohomology group. -/
theorem field_endpoint_isZero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) (n : ℕ) :
    IsZero (_root_.CategoryTheory.Sheaf.LargeCohomology.H.{u + 2, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 1)
      (SmoothSite.base (Spec (.of k)))) :=
  _root_.CategoryTheory.Sheaf.LargeCohomology.isZero_H_succ_base k F n

end Field

#print axioms actual_cover_member_splits
#print axioms actual_henselian_ext_succ_eq_zero
#print axioms original_transfer_field_base_isZero

end MotivicTest.Cohomology.SheafCohomologyHenselianEvaluation
