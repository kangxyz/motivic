/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CycleSymbols
public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Basic

/-!
# Actual finite-point Milnor evaluation in every diagonal weight

The support of an actual point correspondence has its literal finite field of
global functions, with its original scalar map and every original Laurent
coordinate. Its value is the proved finite-extension Milnor norm of that tuple.
Integer-linear extension evaluates the original signed correspondence group.

Rational graph normalization and identity-coordinate vanishing are proved here.
No compatibility with curve boundaries, descent to homology, or substitute
cohomology group is assumed or introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.DiagonalPointNorm
open _root_.AlgebraicGeometry.Scheme

open MilnorK DiagonalCycleSymbols
open WeightOnePointNorm (point)

variable (k : Type u) [Field k]

private instance baseIntegral :
    IsIntegral ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

/-- A genuine integral finite support in the original q-fold torus product. -/
abbrev Generator (q : ℕ) := FiniteCorrespondenceGenerator
  (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) q).hom

variable {k} {q : ℕ} (Z : Generator k q)

/-- The coordinate ring of the whole actual support, not of one coordinate image. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.scheme, ⊤)

/-- Finite projection to the field point makes the original support affine. -/
instance supportAffine : IsAffine Z.scheme := by
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  exact isAffine_of_isAffineHom Z.projection

/-- The original support with its canonical global-section affine chart. -/
def supportIsoSpec : Z.scheme ≅ Spec (coordinateRing Z) := Z.scheme.isoSpec

/-- The scalar map is exactly the pullback of the original source projection. -/
def scalarMap : k →+* coordinateRing Z :=
  Z.projection.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

instance coordinateAlgebra : Algebra k (coordinateRing Z) := (scalarMap Z).toAlgebra

/-- The whole support field has its original finite degree over the base. -/
instance coordinateFinite : Module.Finite k (coordinateRing Z) := by
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  change (scalarMap Z).Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The integral finite support has a field of global functions. -/
theorem coordinateRing_isField : IsField (coordinateRing Z) :=
  isField_of_universallyClosed k Z.projection

noncomputable instance coordinateField : Field (coordinateRing Z) :=
  (coordinateRing_isField Z).toField

/-- Every original Laurent unit is retained, with its position in the tuple. -/
def coordinateUnit (i : Fin q) : (coordinateRing Z)ˣ :=
  Units.map ((Z.targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) q i).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k))

/-- The canonical support chart retains the original scalar map literally. -/
@[reassoc] theorem supportIsoSpec_inv_projection :
    (supportIsoSpec Z).inv ≫ Z.projection =
      Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing Z))) := by
  change Z.scheme.isoSpec.inv ≫
    (show Z.scheme ⟶ Spec (.of k) from Z.projection) = _
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

variable [CharZero k]

/-- The actual finite-extension norm of the original full coordinate tuple. -/
def generatorValue : K k q :=
  finiteExtensionNorm k (coordinateRing Z) q (symbol (coordinateUnit Z))

/-- Additive evaluation on the original signed correspondence group, before
any quotient by identity axes or singular boundaries. -/
def cycleValue (k : Type u) [Field k] [CharZero k] (q : ℕ) :
    (point k ⟶ target k q) →+ K k q :=
  Finsupp.liftAddHom fun Z => zmultiplesHom _ (generatorValue Z)

/-- The original signed multiplicity is retained literally. -/
@[simp] theorem cycleValue_single (Z : Generator k q) (n : ℤ) :
    cycleValue k q (Finsupp.single Z n) = n • generatorValue Z :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The fundamental cycle evaluates by the norm from its actual support field. -/
@[simp] theorem cycleValue_cycle (Z : Generator k q) :
    cycleValue k q Z.cycle = generatorValue Z := by
  change cycleValue k q (Finsupp.single Z 1) = _
  rw [cycleValue_single, one_zsmul]

/-- An identity coordinate kills the symbol in its original finite support field. -/
theorem generatorValue_eq_zero_of_coordinate_one (i : Fin q)
    (hi : coordinateUnit Z i = 1) : generatorValue Z = 0 := by
  rw [generatorValue, symbol_eq_zero_of_eq_one (coordinateUnit Z) i hi, map_zero]

/-- Signed cycles supported on identity-coordinate loci evaluate to zero. -/
theorem cycleValue_eq_zero_of_identity_support
    (α : point k ⟶ target k q)
    (hα : ∀ Z ∈ α.support, ∃ i : Fin q, coordinateUnit Z i = 1) :
    cycleValue k q α = 0 := by
  classical
  conv_lhs => rw [← α.sum_single]
  rw [map_finsuppSum]
  apply Finset.sum_eq_zero
  intro Z hZ
  dsimp only
  obtain ⟨i, hi⟩ := hα Z hZ
  rw [cycleValue_single, generatorValue_eq_zero_of_coordinate_one Z i hi, smul_zero]

section RationalGraphs

omit [CharZero k] in
/-- The original global Laurent coordinates of a rational tuple map. -/
def rationalCoordinate (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) q) (i : Fin q) : kˣ :=
  Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom
    (Units.map ((φ.left ≫ (SmoothSite.torusCoordinate (.of k) q i).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k)))

omit [CharZero k] in
/-- The actual graph generator, with its original finite source projection. -/
abbrev graphSupport (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) q) : Generator k q :=
  graphGeneratorOver (X := Spec (.of k)) φ.left (MorphismProperty.Over.w φ)

omit [CharZero k] in
/-- The actual graph support has degree one for its original scalar map. -/
theorem graph_finrank (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) q) :
    Module.finrank k (coordinateRing (graphSupport φ)) = 1 := by
  apply Module.finrank_of_bijective_algebraMap
  change Function.Bijective (scalarMap (graphSupport φ))
  exact (asIso (graphSupport φ).projection.appTop).commRingCatIsoToRingEquiv.bijective.comp
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.bijective

omit [CharZero k] in
/-- Each support coordinate of an actual graph is its original scalar unit. -/
theorem graph_coordinate (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) q) (i : Fin q) :
    coordinateUnit (graphSupport φ) i =
      Units.map (algebraMap k (coordinateRing (graphSupport φ))).toMonoidHom
        (rationalCoordinate φ i) := by
  apply Units.ext
  change ((graphSupport φ).targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) q i).left).appTop (laurentGlobalUnit (.of k)).val =
    scalarMap (graphSupport φ) (rationalCoordinate φ i : k)
  rw [← graphGeneratorOver_projection_target, Category.assoc, Scheme.Hom.comp_appTop]
  change _ = (graphSupport φ).projection.appTop
    ((Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom
      ((φ.left ≫ (SmoothSite.torusCoordinate (.of k) q i).left).appTop
        (laurentGlobalUnit (.of k)).val)))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
  rfl

/-- Evaluation of an actual graph support is the original Milnor symbol. -/
@[simp] theorem generatorValue_graph (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) q) :
    generatorValue (graphSupport φ) = symbol (rationalCoordinate φ) := by
  have hc : coordinateUnit (graphSupport φ) =
      (Units.map (algebraMap k (coordinateRing (graphSupport φ))).toMonoidHom) ∘
        rationalCoordinate φ := funext (graph_coordinate φ)
  rw [generatorValue, hc, ← map_symbol, finiteExtensionNorm_map_constants,
    graph_finrank, Nat.cast_one, one_smul]

/-- The actual correspondence-category graph, not a replacement generator,
evaluates to its full rational tuple symbol. -/
@[simp] theorem cycleValue_graph (φ : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) q) :
    cycleValue k q ((Cor.graphFunctor k).map φ) = symbol (rationalCoordinate φ) := by
  let : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  rw [Cor.graphFunctor_map, componentGraphCycleOver_eq_graphGeneratorOver_cycle,
    cycleValue_cycle, generatorValue_graph]

omit [CharZero k] in
/-- Every entry of the actual rational tuple is the specified original unit. -/
@[simp] theorem rationalCoordinate_rationalTuple (a : Fin q → kˣ) (i : Fin q) :
    rationalCoordinate (rationalTuple k q a) i = a i := by
  have hc : (rationalTuple k q a).left ≫ (SmoothSite.torusCoordinate (.of k) q i).left =
      (WeightOnePointNorm.rationalTorusPoint k (a i)).left :=
    congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of k) q
      (fun j => WeightOnePointNorm.rationalTorusPoint k (a j)) i)
  have hone : (WeightOnePointNorm.rationalPoint k (a i)).left ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left =
      (WeightOnePointNorm.rationalTorusPoint k (a i)).left :=
    congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of k) 1
      (fun _ => WeightOnePointNorm.rationalTorusPoint k (a i)) 0)
  change Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom
    (Units.map (((rationalTuple k q a).left ≫
      (SmoothSite.torusCoordinate (.of k) q i).left).appTop).hom.toMonoidHom
        (laurentGlobalUnit (.of k))) = _
  rw [hc, ← hone]
  exact WeightOnePointNorm.rationalCoordinate_rationalPoint (a i)

/-- The all-weight finite-point evaluator is a left inverse on every literal
rational tuple graph, including the empty tuple in weight zero. -/
@[simp] theorem cycleValue_rationalTuple (a : Fin q → kˣ) :
    cycleValue k q ((Cor.graphFunctor k).map (rationalTuple k q a)) = symbol a := by
  rw [cycleValue_graph]
  exact congrArg symbol (funext (rationalCoordinate_rationalTuple a))

/-- Any specified identity coordinate kills the actual rational tuple graph. -/
theorem cycleValue_rationalTuple_one (a : Fin q → kˣ) (i : Fin q) (hi : a i = 1) :
    cycleValue k q ((Cor.graphFunctor k).map (rationalTuple k q a)) = 0 := by
  rw [cycleValue_rationalTuple, symbol_eq_zero_of_eq_one a i hi]

end RationalGraphs

end Motivic.DiagonalPointNorm
