/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.AffineLine.Relative.OverlapZero
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.OpenGeometry
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal

/-! # Original relative affine-line higher classes vanish over a generic base open -/

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

/-- Every original ordinary class in degree at least two is killed by actual
base restrictions. The entire relative line remains at all three stages, and
no sheaf or cohomology object over the fraction field is introduced. -/
theorem exists_relative_generic_base_h_add_two_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 2) (lineSite (k := k) (R := R))) :
    ∃ (r : R) (hr : r ≠ 0),
      let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
      ∃ (s : Localization.Away r) (hs : s ≠ 0),
        let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
        ∃ V : (Spec (.of (Localization.Away s))).Opens,
          IsAffineOpen V ∧ genericPoint (Spec (.of (Localization.Away s))) ∈ V ∧
          (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
            F (n + 2)).map
            (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
              (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
                lineMap (IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)) ≫
                lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op x = 0 := by
  let P := presheaf.{w, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) F (n + 2)
  obtain ⟨r, hr, f, hf, hx⟩ := exists_relative_monic_open_restriction_eq_zero F (n + 1) x
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let φ := IsScalarTower.toAlgHom k R (Localization.Away r)
  let x₁ := P.map (lineMap φ).op x
  have hx₁ : P.map (openInclusion f).op x₁ = 0 := by
    simpa only [x₁, ← Functor.map_comp_apply, ← op_comp] using hx
  obtain ⟨s, hs, Y, p, hY, hp, hZ, hA, hYx⟩ :=
    exists_relative_monic_positive_zero_square F (n + 1) f hf x₁ hx₁
  let : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  let : IsAffine Y.left := hY
  let : Etale p.left := hp
  let : IsIso (pullback.snd p.left
      (inclusion (f.map (algebraMap (Localization.Away r) (Localization.Away s))))) := hZ
  let ψ := IsScalarTower.toAlgHom k (Localization.Away r) (Localization.Away s)
  let x₂ := P.map (lineMap ψ).op x₁
  have hY₂ : P.map p.op x₂ = 0 := by
    simpa only [x₂, ← Functor.map_comp_apply, ← op_comp] using hYx
  obtain ⟨t, ht, hx₂⟩ := exists_relativeLine_base_open_restriction_eq_zero_of_zero_square
    F n (f.map (algebraMap (Localization.Away r) (Localization.Away s))) (hf.map _)
      p x₂ hA hY₂
  let V : (Spec (.of (Localization.Away s))).Opens := PrimeSpectrum.basicOpen t
  have hη : genericPoint (Spec (.of (Localization.Away s))) ∈ V := by
    rw [genericPoint_eq_bot_of_affine]
    exact ht
  have hC : boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V =
      relativeLineBaseOpen (k := k) t := by
    exact top_inf_eq _
  have hV : IsAffineOpen V := IsAffineOpen.Spec_basicOpen
    (R := .of (Localization.Away s)) t
  refine ⟨r, hr, s, hs, V, hV, hη, ?_⟩
  change P.map (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
    (relativeLineBaseOpen t)).op x₂ = 0 at hx₂
  change P.map (SmoothSite.openInclusion (lineSite (k := k) (R := Localization.Away s))
    (boundaryBaseSourceOpen (boundaryLineProjection (Localization.Away s)) ⊤ V) ≫
      lineMap ψ ≫ lineMap φ).op x = 0
  rw [hC]
  simpa only [x₂, x₁, ← Functor.map_comp_apply, ← op_comp, Category.assoc] using hx₂

end Motivic.SheafCohomology
