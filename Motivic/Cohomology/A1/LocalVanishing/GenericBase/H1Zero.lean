/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Monic.H1BaseZero

/-! # Every original relative affine-line H¹ class vanishes over a generic base open -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.PolynomialOpenQuotient
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
attribute [local instance] away_smooth

/-- Two actual base localizations followed by an original generic base open.
The entire relative line is retained at every stage. No coefficient extension
or cohomology on a function field occurs. -/
theorem exists_relative_generic_base_h_one_zero
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (lineSite (k := k) (R := R))) :
    ∃ (r : R) (hr : r ≠ 0),
      let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
      ∃ (s : Localization.Away r) (hs : s ≠ 0),
        let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
        ∃ V : (Spec (.of (Localization.Away s))).Opens,
          IsAffineOpen V ∧ genericPoint (Spec (.of (Localization.Away s))) ∈ V ∧
          (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
            ((SheafWithTransfers.toSheaf k).obj F) 1).map
            (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
              (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
                lineMap (IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)) ≫
                lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op x = 0 := by
  let F₀ := (SheafWithTransfers.toSheaf k).obj F
  let P := presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k))) F₀ 1
  obtain ⟨r, hr, f, hf, hx⟩ := exists_relative_monic_open_restriction_eq_zero F₀ 0 x
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let x₁ := P.map (lineMap φ).op x
  have hx₁ : P.map (openInclusion f).op x₁ = 0 := by
    simpa only [x₁, ← Functor.map_comp_apply, ← op_comp] using hx
  obtain ⟨s, hs, Y, p, hY, hp, hZ, hA, hYx⟩ :=
    exists_relative_monic_positive_zero_square F₀ 0 f hf x₁ hx₁
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  let : IsAffine Y.left := hY
  let : Etale p.left := hp
  let : IsIso (pullback.snd p.left
      (inclusion (f.map (algebraMap (Localization.Away r) (Localization.Away s))))) := hZ
  let ψ := IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)
  let x₂ := P.map (lineMap ψ).op x₁
  have hY₂ : P.map p.op x₂ = 0 := by
    simpa only [x₂, ← Functor.map_comp_apply, ← op_comp] using hYx
  obtain ⟨V, hV, hη, hVx⟩ := exists_monic_h_one_base_open_zero F hF
    (f.map (algebraMap (Localization.Away r) (Localization.Away s))) (hf.map _) x₂ p hA hY₂
  refine ⟨r, hr, s, hs, V, hV, hη, ?_⟩
  change P.map (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
    (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V)).op x₂ = 0
      at hVx
  change P.map (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
    (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
      lineMap ψ ≫ lineMap φ).op x = 0
  simpa only [x₂, x₁, ← Functor.map_comp_apply, ← op_comp, Category.assoc] using hVx

end Motivic.SheafCohomology
