/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Puncture.ProjectionLifts
public import Motivic.Cohomology.A1.LocalVanishing.Puncture.PointColimit
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Genuine punctured projection lifts on the unchanged point index -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable {k : Type u} [Field k] {X U : SmoothSite (Spec (.of k))} (j : U ⟶ X)
  (K : Type u) [Field K] (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder (.of k) U).left)
    AddCommGrpCat.{u + 1})]

/-- Genuine stage lifts give surjectivity on the original pointed-puncture colimit. -/
theorem pointedPunctureProjection_colimit_surjective
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hG : PersistentPunctureImageZero j K b p F N) :
    Function.Surjective (colim.map (pointedProjection (.of k) (relativeFieldPoint b K (𝟙 _))
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N)
      (pointedPuncture (.of k) j (relativeFieldPoint b K (𝟙 _))))) := by
  let Φ := relativeFieldPoint b K (𝟙 _)
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N
  let A := pointedPunctureValues (.of k) j Φ P
  let B := pointedCylinderValues (.of k) Φ P (pointedPuncture (.of k) j Φ)
  let τ : A ⟶ B := pointedProjection (.of k) Φ P (pointedPuncture (.of k) j Φ)
  intro x
  obtain ⟨V, α, rfl⟩ := Concrete.colimit_exists_rep B x
  obtain ⟨W, a', f, hf, β, hβ⟩ := exists_pointed_puncture_projection_lift j K b p F
    hF N hN hLow hG V.unop.obj V.unop.val α
  let W' : Φ.fiber.Elements := ⟨a'⟩
  let f' : W' ⟶ V.unop := ⟨f, hf⟩
  let β' : A.obj (op W') := β
  have hβ' : τ.app (op W') β' = B.map f'.op α := hβ
  refine ⟨colimit.ι A (op W') β', ?_⟩
  change (colim.map τ) (colimit.ι A (op W') β') = colimit.ι B V α
  have hι := ConcreteCategory.congr_hom (colimit.ι_map τ (op W')) β'
  have hw := ConcreteCategory.congr_hom (colimit.w B f'.op) α
  simp only [ConcreteCategory.comp_apply] at hι hw
  exact hι.trans ((congrArg (fun z => colimit.ι B (op W') z) hβ').trans hw)

/-- The inverse of the punctured projection is the original zero-section restriction. -/
theorem pointedPunctureProjection_colimit_isIso
    (hF : F.obj.IsA1Invariant) (N : ℕ) (hN : 0 < N)
    (hLow : ∀ q : ℕ, 0 < q → q < N →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hG : PersistentPunctureImageZero j K b p F N) :
    IsIso (colim.map (pointedProjection (.of k) (relativeFieldPoint b K (𝟙 _))
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N)
      (pointedPuncture (.of k) j (relativeFieldPoint b K (𝟙 _))))) := by
  let Φ := relativeFieldPoint b K (𝟙 _)
  let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F) N
  let f := colim.map (pointedProjection (.of k) Φ P (pointedPuncture (.of k) j Φ))
  let s := colim.map (pointedZeroSection (.of k) Φ P (pointedPuncture (.of k) j Φ))
  have hs : f ≫ s = 𝟙 _ := by
    change colim.map _ ≫ colim.map _ = _
    rw [← Functor.map_comp, pointedProjection_zeroSection, CategoryTheory.Functor.map_id]
  let : Epi f := (AddCommGrpCat.epi_iff_surjective f).mpr
    (pointedPunctureProjection_colimit_surjective j K b p F hF N hN hLow hG)
  have hs' : s ≫ f = 𝟙 _ := by
    apply (cancel_epi f).mp
    rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
  exact ⟨⟨s, hs, hs'⟩⟩

end Motivic.FiniteEtaleSite
