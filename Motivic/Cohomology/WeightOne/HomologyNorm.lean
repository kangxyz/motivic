/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.BoundaryNorm

/-!
# The actual weight-one homology norm

The proved annihilation of singular boundaries descends the point norm to the
homology of the canonical raw complex. Graphs of units give actual classes and
prove surjectivity. Injectivity requires the separate interpolation relation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.WeightOneHomologyNorm
open _root_.AlgebraicGeometry.Scheme

open WeightOneBoundaryNorm _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The literal raw norm in the coefficient universe of the actual complex. -/
def liftedRawNorm : (motivicRawBaseComplex k 1).X 1 ⟶
    AddCommGrpCat.of (ULift.{u + 1} (Additive kˣ)) :=
  AddCommGrpCat.ofHom
    { toFun := fun x => ULift.up (rawDegreeZeroNorm k x)
      map_zero' := congrArg ULift.up (map_zero (rawDegreeZeroNorm k))
      map_add' := fun x y => congrArg ULift.up (map_add (rawDegreeZeroNorm k) x y) }

/-- The actual preceding signed differential is annihilated. -/
theorem liftedRawNorm_boundary :
    (motivicRawBaseComplex k 1).d 0 1 ≫ liftedRawNorm k = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact congrArg ULift.up (rawDegreeZeroNorm_boundary k x)

/-- The norm descends through the genuine homology cokernel. -/
def homologyNormHom : (motivicRawBaseComplex k 1).homology 1 ⟶
    AddCommGrpCat.of (ULift.{u + 1} (Additive kˣ)) :=
  ((motivicRawBaseComplex k 1).sc 1).descHomology
    ((motivicRawBaseComplex k 1).iCycles 1 ≫ liftedRawNorm k) (by
      change ((motivicRawBaseComplex k 1).sc 1).toCycles ≫
        (((motivicRawBaseComplex k 1).sc 1).iCycles ≫ liftedRawNorm k) = 0
      rw [← Category.assoc, ShortComplex.toCycles_i]
      change (motivicRawBaseComplex k 1).d ((ComplexShape.up ℤ).prev 1) 1 ≫ _ = 0
      rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
      exact liftedRawNorm_boundary k)

/-- The actual homology norm, valued in the original field's unit group. -/
def homologyNorm : (motivicRawBaseComplex k 1).homology 1 →+ Additive kˣ :=
  (AddEquiv.ulift : ULift.{u + 1} (Additive kˣ) ≃+ Additive kˣ).toAddMonoidHom.comp
    (homologyNormHom k).hom

/-- Its defining equality retains the actual cycle inclusion and class map. -/
theorem homologyNorm_class (x : (motivicRawBaseComplex k 1).cycles 1) :
    homologyNorm k ((motivicRawBaseComplex k 1).homologyπ 1 x) =
      rawDegreeZeroNorm k ((motivicRawBaseComplex k 1).iCycles 1 x) := by
  have h := ((motivicRawBaseComplex k 1).sc 1).π_descHomology
    ((motivicRawBaseComplex k 1).iCycles 1 ≫ liftedRawNorm k) (by
      change ((motivicRawBaseComplex k 1).sc 1).toCycles ≫
        (((motivicRawBaseComplex k 1).sc 1).iCycles ≫ liftedRawNorm k) = 0
      rw [← Category.assoc, ShortComplex.toCycles_i]
      change (motivicRawBaseComplex k 1).d ((ComplexShape.up ℤ).prev 1) 1 ≫ _ = 0
      rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
      exact liftedRawNorm_boundary k)
  exact congrArg ULift.down (ConcreteCategory.congr_hom h x)

/-- The raw weight-one term in degree two vanishes. -/
theorem isZero_raw_X_two : IsZero ((motivicRawBaseComplex k 1).X 2) := by
  let E := toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))
  change IsZero (E.obj ((singularCochainComplex (reducedTorus k 1) 0).X 1))
  exact E.map_isZero (isZero_singularCochainComplex_X (reducedTorus k 1) 0 1 (by decide))

/-- Every actual raw degree-one element is a cycle. -/
theorem raw_outgoing_d_zero : (motivicRawBaseComplex k 1).d 1 2 = 0 :=
  (isZero_raw_X_two k).eq_of_tgt _ _

/-- The canonical map from the top raw term to its actual homology. -/
def rawClass : (motivicRawBaseComplex k 1).X 1 ⟶
    (motivicRawBaseComplex k 1).homology 1 :=
  ((motivicRawBaseComplex k 1).iCyclesIso 1 2 ((ComplexShape.up ℤ).next_eq' rfl)
      (raw_outgoing_d_zero k)).inv ≫
    (motivicRawBaseComplex k 1).homologyπ 1

/-- The descended norm of a raw class is exactly the original norm. -/
theorem homologyNorm_rawClass (x : (motivicRawBaseComplex k 1).X 1) :
    homologyNorm k (rawClass k x) = rawDegreeZeroNorm k x := by
  rw [rawClass, ConcreteCategory.comp_apply, homologyNorm_class]
  have h := ConcreteCategory.congr_hom
    ((motivicRawBaseComplex k 1).iCyclesIso_inv_hom_id 1 2 ((ComplexShape.up ℤ).next_eq' rfl)
      (raw_outgoing_d_zero k)) x
  exact congrArg (rawDegreeZeroNorm k) h

/-- The actual homology class of the graph of a unit. -/
def graphUnitClass (a : kˣ) : (motivicRawBaseComplex k 1).homology 1 :=
  rawClass k ((motivicRawBaseComplexXIso k 1 0).inv
    ((toReducedTorus k 1).hom.app
      (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫
        (Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k a)))))

/-- Graph classes have their original units as norm, without an inverse sign. -/
theorem homologyNorm_graphUnitClass (a : kˣ) :
    homologyNorm k (graphUnitClass k a) = Additive.ofMul a := by
  rw [graphUnitClass, homologyNorm_rawClass, rawDegreeZeroNorm_graph_unit]

/-- The actual homology norm is surjective over every field. -/
theorem homologyNorm_surjective : Function.Surjective (homologyNorm k) := by
  intro a
  exact ⟨graphUnitClass k a.toMul, homologyNorm_graphUnitClass k a.toMul⟩

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The norm on the genuinely defined derived motivic group at the base field. -/
def motivicNorm :
    motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k))) →+ Additive kˣ :=
  (homologyNorm k).comp (motivicRawBaseEvaluationComparison k 1 1).toAddMonoidHom

/-- The actual derived weight-one norm is surjective. -/
theorem motivicNorm_surjective : Function.Surjective (motivicNorm k) :=
  (homologyNorm_surjective k).comp (motivicRawBaseEvaluationComparison k 1 1).surjective

end Motivic.WeightOneHomologyNorm
