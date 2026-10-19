/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.Envelope.Product
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FieldFamilyAcyclic
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Ordinary acyclicity of the existing all-point envelope and its injective retracts -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry
universe w u
namespace Motivic.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
variable (k : Type u) [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (P : SheafWithTransfers.{u + 1} k) (X : SmoothSite (Spec (.of k))) (n : ℕ)

/-- Positive original ordinary cohomology of the actual envelope vanishes. -/
theorem originalGermEnvelope_H_succ_eq_zero
    (e : LargeCohomology.H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toSheaf k).obj (originalGermEnvelope k P)) (n + 1) X) : e = 0 := by
  let : HasExt.{u + 1}
      (Sheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left) AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives _
  let e₁ := EtaleSeparatedFiniteType.cohomologyAtBaseEquiv.{w, u + 1} X
    ((toSheaf k).obj (originalGermEnvelope k P)) (n + 1)
  let e₂ := ((LargeCohomology.presheafFunctor.{u + 1, u + 1, u, u + 1}
    (EtaleSeparatedFiniteType.nisnevichTopology X.left) (n + 1)).mapIso
      (originalEnvelopeProductIso k P X)).app (op (EtaleSeparatedFiniteType.identityObject X))
  apply e₁.injective
  apply (ConcreteCategory.bijective_of_isIso e₂.hom).injective
  rw [map_zero, map_zero]
  exact EtaleSeparatedFiniteType.fieldFamilyProduct_ext_succ_eq_zero
    (fun x : X.left ↦ (X.left.residueField x : Type u)) X.left.fromSpecResidueField
    (SmoothSite.originalResidueCoefficient X ((toSheaf k).obj P))
    (EtaleSeparatedFiniteType.identityObject X) n (e₂.hom (e₁ e))

/-- A transfer-injective is ordinarily acyclic because it retracts from its actual envelope.
No ordinary-injectivity or homotopy-invariance assertion is made. -/
theorem injective_underlying_H_succ_eq_zero [Injective P]
    (e : LargeCohomology.H.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj P) (n + 1) X) : e = 0 := by
  obtain ⟨r, hr⟩ := exists_originalGermEnvelope_retraction k P
  let Q := LargeCohomology.presheafFunctor.{w, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) (n + 1) ⋙
    (evaluation (SmoothSite (Spec (.of k)))ᵒᵖ AddCommGrpCat).obj (op X)
  have hid : Q.map ((toSheaf k).map (toOriginalGermEnvelope k P)) ≫
      Q.map ((toSheaf k).map r) = 𝟙 _ := by
    rw [← Q.map_comp, ← (toSheaf k).map_comp, hr, (toSheaf k).map_id, Q.map_id]
  have he := originalGermEnvelope_H_succ_eq_zero k P X n
    (Q.map ((toSheaf k).map (toOriginalGermEnvelope k P)) e)
  have hh := ConcreteCategory.congr_hom hid e
  change Q.map ((toSheaf k).map r)
    (Q.map ((toSheaf k).map (toOriginalGermEnvelope k P)) e) = e at hh
  rw [he, map_zero] at hh
  exact hh.symm

end Motivic.SheafWithTransfers
