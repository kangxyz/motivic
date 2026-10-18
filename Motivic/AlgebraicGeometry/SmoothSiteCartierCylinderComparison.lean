/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothCartierEtaleComparisonOverBase
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionComplement
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichPullbacks

/-! # Actual smooth-site Cartier cylinder charts

The native comparison uses the affine line as the first pullback factor. The
canonical pullback symmetry transports it to the literal cylinder used by
contraction. Both full closed-fiber squares and the ground-field maps are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace Motivic.SmoothSite

variable {k : Type u} [Field k]

/-- The canonical exchange of factors in the two literal cylinder conventions. -/
def nativeCylinderIso (D : SmoothSite (Spec (.of k))) :
    Scheme.Hom.cylinder k D.hom ≅ (a1Cylinder (.of k) D).left :=
  pullbackSymmetry _ _

/-- Pullback symmetry preserves the original zero section, not only its image. -/
@[reassoc (attr := simp)]
theorem cylinderZeroSection_nativeCylinderIso (D : SmoothSite (Spec (.of k))) :
    Scheme.Hom.cylinderZeroSection k D.hom ≫ (nativeCylinderIso D).hom =
      (a1Section (.of k) D 0).left := by
  change Scheme.Hom.cylinderZeroSection k D.hom ≫
      (pullbackSymmetry (Scheme.PolynomialLaurent.polynomialProjection (.of k)) D.hom).hom =
    (show D.left ⟶ pullback D.hom (Scheme.PolynomialLaurent.polynomialProjection (.of k)) from
      (a1Section (.of k) D 0).left)
  apply pullback.hom_ext
  · have h : Scheme.Hom.cylinderZeroSection k D.hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
          D.hom = 𝟙 (D.left) := by
      dsimp only [Scheme.Hom.cylinderZeroSection]
      exact pullback.lift_snd _ _ _
    simpa [a1Section, productLift, Scheme.PolynomialLaurent.polynomialProjection] using h
  · have h : Scheme.Hom.cylinderZeroSection k D.hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
          D.hom = D.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
      dsimp only [Scheme.Hom.cylinderZeroSection]
      exact pullback.lift_fst _ _ _
    simpa [a1Section, productLift, affineLinePoint, homMk,
      Scheme.PolynomialLaurent.polynomialProjection] using h

/-- An actual open of a smooth closed pair, with its original field structure. -/
def closedOpenSite {Y : SmoothSite (Spec (.of k))} {Z : Scheme.{u}}
    (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)] (O : Z.Opens) :
    SmoothSite (Spec (.of k)) := by
  let : IsNoetherian Z := isNoetherian_of_finiteType i
  exact mk (O.ι ≫ i ≫ Y.hom)

/-- Every point of an actual smooth Cartier pair has a common étale comparison
with its own literal contraction cylinder. The two squares retain the entire
original closed fiber; no perfect-field or supplied-chart hypothesis is used. -/
theorem exists_cartier_cylinder_comparison
    (Y : SmoothSite (Spec (.of k))) {Z : Scheme.{u}}
    (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i)) (z : Z) :
    ∃ O : Z.Opens, z ∈ O ∧
      ∃ (V : SmoothSite (Spec (.of k))) (a : V ⟶ Y)
        (b : V ⟶ a1Cylinder (.of k) (closedOpenSite (Y := Y) i O))
        (d : closedOpenSite (Y := Y) i O ⟶ V),
        Etale a.left ∧ Etale b.left ∧
        IsPullback d.left O.ι a.left i ∧
        IsPullback d.left (𝟙 _) b.left
          (a1Section (.of k) (closedOpenSite (Y := Y) i O) 0).left := by
  obtain ⟨U, _hU, hz, V, a, b, d, ha, hb, hpa, hpb, _hia, _hib,
      hbase, hsa, hsb, hqa, hqb⟩ :=
    Scheme.exists_smooth_cartier_etale_cylinder_comparison_over_base i Y.hom hI z
  let : Etale a := ha
  let : Etale b := hb
  let : IsSeparated a := hsa
  let : IsSeparated b := hsb
  let : QuasiCompact a := hqa
  let : QuasiCompact b := hqb
  let O := i ⁻¹ᵁ U
  let D := closedOpenSite (Y := Y) i O
  let T : SmoothSite (Spec (.of k)) := mk (a ≫ U.ι ≫ Y.hom)
  let a' : T ⟶ Y := homMk (a ≫ U.ι) (Category.assoc _ _ _)
  let b' : T ⟶ a1Cylinder (.of k) D := homMk
    (b ≫ (nativeCylinderIso D).hom) (by
      change (b ≫ (pullbackSymmetry _ _).hom) ≫
        (pullback.fst _ _ ≫ D.hom) = a ≫ U.ι ≫ Y.hom
      rw [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc]
      exact hbase.symm)
  let d' : D ⟶ T := homMk d (by
    change d ≫ a ≫ U.ι ≫ Y.hom = O.ι ≫ i ≫ Y.hom
    rw [← Category.assoc d a, hpa.w, Category.id_comp, morphismRestrict_ι_assoc])
  have hswap : IsPullback (Scheme.Hom.cylinderZeroSection k D.hom)
      (𝟙 (D.left)) (nativeCylinderIso D).hom (a1Section (.of k) D 0).left := by
    change IsPullback (Scheme.Hom.cylinderZeroSection k (O.ι ≫ i ≫ Y.hom))
      (𝟙 O.toScheme)
      (pullbackSymmetry (Scheme.PolynomialLaurent.polynomialProjection (.of k))
        (O.ι ≫ i ≫ Y.hom)).hom (a1Section (.of k) D 0).left
    apply IsPullback.of_vert_isIso
    exact ⟨(cylinderZeroSection_nativeCylinderIso D).trans (Category.id_comp _).symm⟩
  refine ⟨O, hz, T, a', b', d', ?_, ?_, ?_, ?_⟩
  · change Etale (a ≫ U.ι)
    infer_instance
  · change Etale (b ≫ (nativeCylinderIso D).hom)
    infer_instance
  · change IsPullback d (i ⁻¹ᵁ U).ι (a ≫ U.ι) i
    simpa only [Category.id_comp] using hpa.paste_vert (isPullback_morphismRestrict i U)
  · change IsPullback d (𝟙 (D.left)) (b ≫ (nativeCylinderIso D).hom)
      (a1Section (.of k) D 0).left
    simpa only [Category.id_comp] using hpb.paste_vert hswap

end Motivic.SmoothSite
