/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.ProjectiveImage
/-! # The same schematic image of the original quadratic map and its generic point -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjectiveSpace _root_.MvPolynomial
universe u
namespace AlgebraicGeometry.Scheme
variable {A B : Type u} [CommRing A] [CommRing B]
/-- An injective original affine ring map has zero schematic kernel. -/
theorem ker_SpecMap_eq_bot_of_injective (φ : A →+* B) (hφ : Function.Injective φ) :
    (Spec.map (CommRingCat.ofHom φ)).ker = ⊥ := by
  rw [ker_of_isAffine]
  have hc : (ΓSpecIso (.of A)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop ≫
      (ΓSpecIso (.of B)).hom = CommRingCat.ofHom φ := by
    rw [← ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hi : Function.Injective (Spec.map (CommRingCat.ofHom φ)).appTop := by
    intro a b hab
    apply (ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.injective
    apply hφ
    have ha := ConcreteCategory.congr_hom hc ((ΓSpecIso (.of A)).hom a)
    have hb := ConcreteCategory.congr_hom hc ((ΓSpecIso (.of A)).hom b)
    change φ ((ΓSpecIso (.of A)).hom a) = φ ((ΓSpecIso (.of A)).hom b)
    refine ha.symm.trans (Eq.trans ?_ hb)
    change (ΓSpecIso (.of B)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((ΓSpecIso (.of A)).inv ((ΓSpecIso (.of A)).hom a))) =
      (ΓSpecIso (.of B)).hom
        ((Spec.map (CommRingCat.ofHom φ)).appTop
          ((ΓSpecIso (.of A)).inv ((ΓSpecIso (.of A)).hom b)))
    simp only [Iso.hom_inv_id_apply]
    exact congrArg (fun x => (ΓSpecIso (.of B)).hom x) hab
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hi]
  ext1
  funext U
  simp [IdealSheafData.ofIdealTop_ideal]
end AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} (g : σ → R)

/-- The original quadratic affine coordinate map, before passage to the fraction field. -/
def quadraticConstantChartMap : coordinateRing k (Exponent σ) constantIndex →+* R :=
  (aeval (fun e : {e : Exponent σ // e ≠ constantIndex} =>
    monomialFunction k R g e.val)).toRingHom.comp
      (coordinateRingEquivPolynomial k (Exponent σ) constantIndex).toRingHom

/-- The original map of the entire affine scheme using its unchanged quadratic coordinates. -/
def quadraticOriginalMap : Spec (.of R) ⟶ ProjectiveSpace k (Exponent σ) :=
  Spec.map (CommRingCat.ofHom (quadraticConstantChartMap k R g)) ≫
    quadraticChartInclusion k constantIndex

theorem quadraticConstantChartMap_fraction :
    (algebraMap R (FractionRing R)).comp (quadraticConstantChartMap k R g) =
      nativeDehomogenization k R g constantIndex := by
  apply RingHom.ext
  intro z
  change algebraMap R (FractionRing R)
    (aeval _ (coordinateRingToPolynomial k (Exponent σ) constantIndex z)) = _
  have h : (algebraMap R (FractionRing R)).comp
      (aeval (fun e : {e : Exponent σ // e ≠ constantIndex} =>
        monomialFunction k R g e.val)).toRingHom =
      (dehomogenizedEvaluation k R g constantIndex).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [dehomogenizedEvaluation, IsScalarTower.algebraMap_apply k R (FractionRing R)]
    · intro e
      simp [dehomogenizedEvaluation, ratio]
  exact RingHom.congr_fun h _

@[reassoc]
theorem quadraticOriginalMap_generic :
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
      quadraticOriginalMap k R g = quadraticProjectiveGenericMap k R g := by
  rw [quadraticOriginalMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quadraticConstantChartMap_fraction]
  rfl

/-- Passing to the generic point does not alter the actual schematic closure. -/
theorem quadraticOriginalMap_ker :
    (quadraticOriginalMap k R g).ker = (quadraticProjectiveGenericMap k R g).ker := by
  rw [← quadraticOriginalMap_generic, Scheme.Hom.ker_comp,
    Scheme.ker_SpecMap_eq_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)),
    Scheme.IdealSheafData.map_bot]

end QuadraticIncidence.InfinityChart
