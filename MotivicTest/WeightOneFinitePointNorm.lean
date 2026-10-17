/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneFinitePointNorm
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual finite point norm

The original finite field may strictly contain the coordinate-generated image
field. These consumers retain the geometric residue degree, literal scalar maps,
whole fundamental pushforward, and arbitrary signed multiplicity. No separability
or closed-immersion hypothesis on the original point is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic Motivic.WeightOnePointNorm Motivic.WeightOneFundamentalNorm
open Motivic.WeightOneFinitePointNorm

universe u

namespace MotivicTest.WeightOneFinitePointNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The original whole extension-field fundamental cycle is actually pushed forward. -/
theorem whole_fundamental_pushforward (b : Eˣ) :
    FiniteCorrespondence.toIntegralCycle (unitPointCorrespondence (k := k) b) =
      IntegralCycle.finitePushforward (unitPoint (k := k) b)
        (fundamentalCycle (Spec (.of E))) :=
  toIntegralCycle_unitPointCorrespondence b

/-- The finite point norm is the determinant norm, even without a primitive coordinate. -/
theorem arbitrary_unit_norm (b : Eˣ) :
    cycleNorm k (unitPointCorrespondence (k := k) b) =
      Additive.ofMul (Units.map (Algebra.norm k) b) :=
  cycleNorm_unitPointCorrespondence b

/-- The scalar determinant value is retained in the original base field. -/
theorem arbitrary_unit_norm_value (b : Eˣ) :
    ((cycleNorm k (unitPointCorrespondence (k := k) b)).toMul : k) =
      Algebra.norm k (b : E) := by
  rw [cycleNorm_unitPointCorrespondence]
  rfl

/-- A unit already in the base still carries the entire extension degree.
In particular one cannot replace the original field by its coordinate image. -/
theorem base_unit_retains_extension_degree (a : kˣ) :
    cycleNorm k (unitPointCorrespondence (k := k)
      (Units.map (algebraMap k E).toMonoidHom a)) =
      Additive.ofMul (a ^ Module.finrank k E) := by
  rw [cycleNorm_unitPointCorrespondence]
  congr 1
  apply Units.ext
  exact Algebra.norm_algebraMap (a : k)

/-- Arbitrary signed point multiplicities are retained by the same genuine cycle norm. -/
theorem signed_unit_norm (b : Eˣ) (n : ℤ) :
    cycleNorm k (n • unitPointCorrespondence (k := k) b) =
      n • Additive.ofMul (Units.map (Algebra.norm k) b) := by
  rw [map_zsmul, cycleNorm_unitPointCorrespondence]

/-- The arbitrary-representative adapter assumes the original cycle equality,
never a norm-valued replacement condition. -/
theorem arbitrary_actual_representative (b : Eˣ) (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward (unitPoint (k := k) b)
        (fundamentalCycle (Spec (.of E)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k) b) :=
  cycleNorm_eq_norm_of_unitPoint b α hα

variable (j : Spec (.of E) ⟶ ambient k) [IsFinite j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The actual geometric residue degree is the full degree over the image field. -/
theorem actual_image_degree (x : Spec (.of E)) :
    j.residueDegree x = Module.finrank (coordinateRing (imageGenerator j hj)) E :=
  residueDegree_eq_image_finrank j hj x

/-- The finite image field inclusion preserves precisely the original base scalar map. -/
theorem original_scalar_tower :
    (imageScalarMap j hj).comp (algebraMap k (coordinateRing (imageGenerator j hj))) =
      algebraMap k E :=
  imageScalarMap_comp j hj

/-- The affine coordinate is pulled back through the original source-to-image map. -/
theorem original_coordinate_pullback :
    imageScalarMap j hj
      (coordinateUnit (imageGenerator j hj) : coordinateRing (imageGenerator j hj)) =
      (affineCoordinateUnit j : E) :=
  imageScalarMap_coordinate j hj

include hj in
/-- Closed immersion of the original source point is not needed. -/
theorem finite_map_fundamental_norm (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) :=
  cycleNorm_eq_norm_of_finite_fundamental j hj α hα

end MotivicTest.WeightOneFinitePointNorm

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOneFinitePointNorm.imageGenerator,
      `Motivic.WeightOneFinitePointNorm.imageGenerator_toImage_projection,
      `Motivic.WeightOneFinitePointNorm.imageGenerator_support,
      `Motivic.WeightOneFinitePointNorm.finitePointCorrespondence,
      `Motivic.WeightOneFinitePointNorm.toIntegralCycle_finitePointCorrespondence,
      `Motivic.WeightOneFinitePointNorm.imageScalarMap,
      `Motivic.WeightOneFinitePointNorm.imageAlgebra,
      `Motivic.WeightOneFinitePointNorm.imageScalarMap_comp,
      `Motivic.WeightOneFinitePointNorm.imageScalarTower,
      `Motivic.WeightOneFinitePointNorm.imageScalarMap_coordinate,
      `Motivic.WeightOneFinitePointNorm.imageField,
      `Motivic.WeightOneFinitePointNorm.imageFinite,
      `Motivic.WeightOneFinitePointNorm.toImage_isoSpec,
      `Motivic.WeightOneFinitePointNorm.norm_imageScalarMap,
      `Motivic.WeightOneFinitePointNorm.normUnits_imageScalarMap,
      `Motivic.WeightOneFinitePointNorm.residueDegree_eq_image_finrank,
      `Motivic.WeightOneFinitePointNorm.cycleNorm_finitePointCorrespondence,
      `Motivic.WeightOneFinitePointNorm.cycleNorm_eq_norm_of_finite_fundamental,
      `Motivic.WeightOneFinitePointNorm.cycleNorm_eq_norm_unit_of_finite_fundamental,
      `Motivic.WeightOneFinitePointNorm.unitTorusPoint,
      `Motivic.WeightOneFinitePointNorm.unitTorusPoint_projection,
      `Motivic.WeightOneFinitePointNorm.unitPoint,
      `Motivic.WeightOneFinitePointNorm.unitPoint_projection,
      `Motivic.WeightOneFinitePointNorm.unitPoint_finite,
      `Motivic.WeightOneFinitePointNorm.unitPoint_ambientCoordinate,
      `Motivic.WeightOneFinitePointNorm.affineCoordinateUnit_unitPoint,
      `Motivic.WeightOneFinitePointNorm.unitPointCorrespondence,
      `Motivic.WeightOneFinitePointNorm.toIntegralCycle_unitPointCorrespondence,
      `Motivic.WeightOneFinitePointNorm.cycleNorm_unitPointCorrespondence,
      `Motivic.WeightOneFinitePointNorm.cycleNorm_eq_norm_of_unitPoint,
      `MotivicTest.WeightOneFinitePointNorm.whole_fundamental_pushforward,
      `MotivicTest.WeightOneFinitePointNorm.arbitrary_unit_norm,
      `MotivicTest.WeightOneFinitePointNorm.arbitrary_unit_norm_value,
      `MotivicTest.WeightOneFinitePointNorm.base_unit_retains_extension_degree,
      `MotivicTest.WeightOneFinitePointNorm.signed_unit_norm,
      `MotivicTest.WeightOneFinitePointNorm.arbitrary_actual_representative,
      `MotivicTest.WeightOneFinitePointNorm.actual_image_degree,
      `MotivicTest.WeightOneFinitePointNorm.original_scalar_tower,
      `MotivicTest.WeightOneFinitePointNorm.original_coordinate_pullback,
      `MotivicTest.WeightOneFinitePointNorm.finite_map_fundamental_norm] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite-point norms and full image degrees use only standard Lean foundations."
