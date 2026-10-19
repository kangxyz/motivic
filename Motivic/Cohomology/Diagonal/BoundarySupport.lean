/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.BoundaryNorm
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.MilnorK.NormalizedAffineEndpointNorm

/-! # Actual all-weight integral one-simplex support algebras -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u
namespace Motivic.DiagonalBoundarySupport
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Normalization
variable (k : Type u) [Field k] (q : ℕ)

/-- The actual integral supports of a one-simplex correspondence. -/
abbrev Generator := FiniteCorrespondenceGenerator
  (_root_.AlgebraicSimplex.smoothSiteObj k 1).hom (SmoothSite.torusPower (.of k) q).hom

private instance simplexIntegral :
    IsIntegral ((𝟭 Scheme).obj (_root_.AlgebraicSimplex.smoothSiteObj k 1).left) :=
  inferInstanceAs (IsIntegral (Spec (.of (_root_.AlgebraicSimplex.CoordinateRing k 1))))

private instance simplexAffine :
    IsAffine ((𝟭 Scheme).obj (_root_.AlgebraicSimplex.smoothSiteObj k 1).left) :=
  inferInstanceAs (IsAffine (Spec (.of (_root_.AlgebraicSimplex.CoordinateRing k 1))))

/-- Polynomial scalars identify the literal global functions on the actual simplex. -/
def simplexGlobalEquiv : Γ((_root_.AlgebraicSimplex.smoothSiteObj k 1).left, ⊤) ≃+* k[X] :=
  (Scheme.ΓSpecIso (.of (_root_.AlgebraicSimplex.CoordinateRing k
      1))).commRingCatIsoToRingEquiv.trans
    (WeightOneBoundaryNorm.oneCoordinateEquiv k).toRingEquiv

variable {k q} (Z : Generator k q)

/-- Global functions of the whole actual integral support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.scheme, ⊤)

instance supportAffine : IsAffine Z.scheme := isAffine_of_isAffineHom Z.projection

/-- The literal polynomial scalar map is induced by the finite source projection. -/
def scalarMap : k[X] →+* coordinateRing Z :=
  Z.projection.appTop.hom.comp (simplexGlobalEquiv k).symm.toRingHom

instance coordinateAlgebra : Algebra k[X] (coordinateRing Z) := (scalarMap Z).toAlgebra

/-- Finite source projection gives finite generation over the actual polynomial coordinate. -/
instance coordinateFinite : Module.Finite k[X] (coordinateRing Z) := by
  change (scalarMap Z).Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _ (simplexGlobalEquiv k).symm.surjective)

/-- Surjectivity over the reduced simplex makes the actual scalar map injective. -/
theorem scalarMap_injective : Function.Injective (scalarMap Z) := by
  let : Surjective Z.projection := ⟨Z.projection_surjective⟩
  let : IsSchemeTheoreticallyDominant Z.projection :=
    IsSchemeTheoreticallyDominant.of_isDominant Z.projection
  have h : Function.Injective Z.projection.appTop := by
    rw [RingHom.injective_iff_ker_eq_bot,
      ← Z.projection.ker_apply ⟨⊤, isAffineOpen_top _⟩, Z.projection.ker_eq_bot]
    simp
  exact h.comp (simplexGlobalEquiv k).symm.injective

/-- The integral support is torsion-free for the literal polynomial action. -/
instance coordinateTorsionFree : Module.IsTorsionFree k[X] (coordinateRing Z) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r b h
  change scalarMap Z r * b = 0 at h
  rcases mul_eq_zero.mp h with hr | hb
  · exact Or.inl ((scalarMap_injective Z) (hr.trans (map_zero _).symm))
  · exact Or.inr hb

/-- The actual finite torsion-free support algebra is free over the PID `k[X]`. -/
instance coordinateFree : Module.Free k[X] (coordinateRing Z) :=
  Module.free_of_finite_type_torsion_free'

/-- The actual projection is flat, derived from integrality and finite projection. -/
instance projectionFlat : Flat Z.projection := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  have h : (scalarMap Z).Flat := by
    change Module.Flat k[X] (coordinateRing Z)
    infer_instance
  have he : Z.projection.appTop.hom =
      (scalarMap Z).comp (simplexGlobalEquiv k).toRingHom := by
    ext r
    simp [scalarMap]
  rw [he]
  exact (RingHom.Flat.of_bijective (simplexGlobalEquiv k).bijective).comp h

/-- The actual support affine chart intertwines its source map with polynomial scalars. -/
theorem supportIsoSpec_projection :
    Z.scheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (scalarMap Z)) =
      Z.projection ≫ (WeightOneBoundaryNorm.oneSchemeIso k).hom := by
  have h : Spec.map (CommRingCat.ofHom (scalarMap Z)) =
      Spec.map Z.projection.appTop ≫
        Spec.map (CommRingCat.ofHom (simplexGlobalEquiv k).symm.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  rw [h, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc]
  congr 1
  change (Spec (.of (_root_.AlgebraicSimplex.CoordinateRing k 1))).isoSpec.hom ≫ _ = _
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change (Scheme.ΓSpecIso (.of (_root_.AlgebraicSimplex.CoordinateRing k 1))).hom
    ((Scheme.ΓSpecIso (.of (_root_.AlgebraicSimplex.CoordinateRing k 1))).inv
      ((WeightOneBoundaryNorm.oneCoordinateEquiv k).symm p)) = _
  simp


/-- Each original torus coordinate is a genuine unit on the whole integral support. -/
def coordinateUnit (i : Fin q) : (coordinateRing Z)ˣ :=
  Units.map ((Z.targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) q i).left).appTop).hom.toMonoidHom
      (Scheme.PolynomialLaurent.laurentGlobalUnit (.of k))

/-- The original finite support retains a faithful polynomial parameter. -/
instance coordinateFaithful : FaithfulSMul k[X] (coordinateRing Z) :=
  (faithfulSMul_iff_algebraMap_injective k[X] (coordinateRing Z)).mpr
    (scalarMap_injective Z)

variable [CharZero k]

/-- The original support's full normalized endpoint sum, with all coordinate units. -/
def normalizedEndpointValue (a : k) : MilnorK.K k q := by
  let B := coordinateRing Z
  let := FiniteCurve.ring_isDedekindDomain (k := k) B
  let := FiniteCurve.ring_finite_base (k := k) B
  let := FiniteCurveNormalization.normalizationTorsionFree k B
  let := FiniteCurveNormalization.rationalAlgebra k B
  exact MilnorK.DedekindResidue.endpointWeightedResidueSum k
    (FiniteCurve.ring B) (FractionRing B) a q
    (Units.map (algebraMap B (FiniteCurve.ring B)).toMonoidHom ∘
      coordinateUnit Z)

/-- Every positive-weight original one-simplex support has equal normalized
endpoint evaluations; no smoothness or boundary-vanishing premise is used. -/
theorem normalizedEndpointValue_eq {n : ℕ} (Z : Generator k (n + 1)) (a b : k) :
    normalizedEndpointValue Z a = normalizedEndpointValue Z b := by
  exact FiniteCurveNormalization.normalized_endpoint_sum_eq k (coordinateRing Z) a b n
    (coordinateUnit Z)

end Motivic.DiagonalBoundarySupport
