/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.FieldTopDegree
public import Motivic.Cohomology.WeightOne.InterpolationCycle
public import Motivic.Cohomology.WeightOne.SplitPolynomialCycle
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Bilinear rational-point symbols in actual weight-two motivic cohomology

The literal two-coordinate graph classes are multiplicative in each unit.
The proof postcomposes the existing finite-flat quadratic interpolation with
fixed-coordinate graph maps. It does not use a general correspondence product,
assert the Steinberg relation, or claim a Milnor K-theory comparison.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open scoped TensorProduct

universe w u

namespace Motivic.WeightTwoSymbols
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.SingularComplex

open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open WeightOnePointNorm
open WeightOneBoundaryNorm
open WeightOneInterpolationCycle WeightOneSplitPolynomialCycle

variable (k : Type u) [Field k]

/-- The actual two-fold torus in the correspondence category. -/
abbrev target : Cor k := Cor.mk (SmoothSite.torusPower (.of k) 2)

/-- The top raw term has no outgoing differential. -/
theorem raw_outgoing_d_zero : (motivicRawBaseComplex k 2).d 2 3 = 0 := by
  exact (FieldTopDegree.isZero_raw_X k 3 2 (by decide)).eq_of_tgt _ _

/-- The canonical class map of the actual raw degree-two term. -/
def rawClass : (motivicRawBaseComplex k 2).X 2 ⟶
    (motivicRawBaseComplex k 2).homology 2 :=
  ((motivicRawBaseComplex k 2).iCyclesIso 2 3 ((ComplexShape.up ℤ).next_eq' rfl)
      (raw_outgoing_d_zero k)).inv ≫
    (motivicRawBaseComplex k 2).homologyπ 2

/-- The canonical raw class map annihilates its actual preceding differential. -/
theorem differential_rawClass :
    (motivicRawBaseComplex k 2).d 1 2 ≫ rawClass k = 0 := by
  rw [rawClass, ← (motivicRawBaseComplex k 2).toCycles_i 1 2]
  simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

private theorem raw_d (q r t : ℕ) :
    (motivicRawBaseComplex k q).d (Indexing.singularDegree q r)
        (Indexing.singularDegree q t) =
      (-1 : ℤ) ^ q • ((motivicRawBaseComplexXIso k q r).hom ≫
        (singularObj (reducedTorus k q) (WeightOnePointNorm.point k)).d r t ≫
          (motivicRawBaseComplexXIso k q t).inv) := by
  let E := toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))
  calc
    _ = E.map (((singularCochainComplex (reducedTorus k q) 0)⟦-(q : ℤ)⟧).d
        (Indexing.singularDegree q r) (Indexing.singularDegree q t)) := by
      simp only [CochainComplex.shiftFunctor_obj_d', Units.smul_def,
        CategoryTheory.Functor.map_zsmul]
      rfl
    _ = _ := by
      change E.map
          ((((singularComplex (reducedTorus k q)).extend
            (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
              ((q : ℤ) - r) ((q : ℤ) - t)) =
        (-1 : ℤ) ^ q •
          (E.map (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q r rfl).hom ≫
            E.map ((singularComplex (reducedTorus k q)).d r t) ≫
            E.map (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q t rfl).inv)
      simpa only [Units.smul_def, CategoryTheory.Functor.map_zsmul,
        CategoryTheory.Functor.map_comp, Int.negOnePow_neg, Int.coe_negOnePow_natCast] using
        congrArg (fun f => E.map f)
          (_root_.HomologicalComplex.ExtensionSignedShift.shifted_d (singularComplex (reducedTorus k
              q)) q r t)

/-- The weight-two signed shift has positive sign on the endpoint differential. -/
theorem raw_d_one_two :
    (motivicRawBaseComplex k 2).d 1 2 =
      (motivicRawBaseComplexXIso k 2 1).hom ≫
        (singularObj (reducedTorus k 2) (point k)).d 1 0 ≫
          (motivicRawBaseComplexXIso k 2 0).inv := by
  have h := raw_d k 2 1 0
  change (motivicRawBaseComplex k 2).d 1 2 =
    (1 : ℤ) • ((motivicRawBaseComplexXIso k 2 1).hom ≫
      (singularObj (reducedTorus k 2) (point k)).d 1 0 ≫
        (motivicRawBaseComplexXIso k 2 0).inv) at h
  simpa only [one_zsmul] using h

/-- The two-face singular differential before the weight-two shift. -/
theorem singular_d_one_zero :
    (singularObj (reducedTorus k 2) (point k)).d 1 0 =
      transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ (0 : Fin 2)) -
      transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ (1 : Fin 2)) :=
  SingularComplex.obj_d_one_zero _ _

/-- Class map on the literal reduced zero-simplex group. -/
def singularClass : sections (reducedTorus k 2)
    (Cor.simplexProduct (point k) 0) →+
      (motivicRawBaseComplex k 2).homology 2 :=
  (rawClass k).hom.comp (motivicRawBaseComplexXIso k 2 0).inv.hom

/-- Singular boundaries vanish in the actual shifted weight-two homology. -/
theorem singularClass_boundary
    (s : sections (reducedTorus k 2) (Cor.simplexProduct (point k) 1)) :
    singularClass k ((singularObj (reducedTorus k 2) (point k)).d 1 0 s) = 0 := by
  have h := ConcreteCategory.congr_hom (differential_rawClass k)
    ((motivicRawBaseComplexXIso k 2 1).inv s)
  rw [raw_d_one_two] at h
  change rawClass k ((motivicRawBaseComplexXIso k 2 0).inv
    ((singularObj (reducedTorus k 2) (point k)).d 1 0
      ((motivicRawBaseComplexXIso k 2 1).hom
        ((motivicRawBaseComplexXIso k 2 1).inv s)))) = 0 at h
  rw [Iso.inv_hom_id_apply] at h
  exact h

/-- Actual signed point correspondences map to their genuine homology classes. -/
def cycleClass : (point k ⟶ target k) →+
    (motivicRawBaseComplex k 2).homology 2 :=
  (singularClass k).comp
    (((toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 0))).hom.comp
      ((AddEquiv.ulift : ULift.{u + 1}
        (Cor.simplexProduct (point k) 0 ⟶ target k) ≃+
          (Cor.simplexProduct (point k) 0 ⟶ target k)).symm.toAddMonoidHom.comp
        (Preadditive.leftComp (target k) (zeroProductIso k).hom)))

/-- The actual quotient class of a represented zero-simplex. -/
theorem singularClass_quotient (α : Cor.simplexProduct (point k) 0 ⟶ target k) :
    singularClass k ((toReducedTorus k 2).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up α)) =
        cycleClass k ((zeroProductIso k).inv ≫ α) := by
  change _ = singularClass k ((toReducedTorus k 2).hom.app
    (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ (zeroProductIso k).inv ≫ α)))
  rw [Iso.hom_inv_id_assoc]

/-- A literal coface evaluates to its original endpoint cycle. -/
theorem singularClass_face_quotient (i : Fin 2)
    (α : Cor.simplexProduct (point k) 1 ⟶ target k) :
    singularClass k (transfer (reducedTorus k 2)
      ((Cor.simplexProductCosimplicial (point k)).δ i)
        ((toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) =
      cycleClass k ((zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (point k)).δ i ≫ α) := by
  exact (congrArg (singularClass k) (reducedTorus_transfer_apply k 2
    ((Cor.simplexProductCosimplicial (point k)).δ i) α)).trans
      (singularClass_quotient k _)

/-- The two full endpoint cycles of any actual singular correspondence have equal classes. -/
theorem cycleClass_endpoints (α : Cor.simplexProduct (point k) 1 ⟶ target k) :
    cycleClass k ((zeroProductIso k).inv ≫
      (Cor.simplexProductCosimplicial (point k)).δ 0 ≫ α) =
    cycleClass k ((zeroProductIso k).inv ≫
      (Cor.simplexProductCosimplicial (point k)).δ 1 ≫ α) := by
  have h := singularClass_boundary k ((toReducedTorus k 2).hom.app
    (op (Cor.simplexProduct (point k) 1)) (ULift.up α))
  rw [singular_d_one_zero] at h
  change singularClass k
    (transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ 0)
      ((toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α)) -
    transfer (reducedTorus k 2) ((Cor.simplexProductCosimplicial (point k)).δ 1)
      ((toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) = 0 at h
  rw [map_sub, singularClass_face_quotient, singularClass_face_quotient, sub_eq_zero] at h
  exact h

/-- Every identity-axis cycle vanishes before passing to homology. -/
theorem cycleClass_axis (i : Fin 2) (α : point k ⟶ WeightOnePointNorm.target k) :
    cycleClass k (α ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (.of k) 1 i)) = 0 := by
  have h := congrArg (fun η => η.hom.app
      (op (Cor.simplexProduct (point k) 0)))
    (torusIdentityAxis_toReducedTorus k 2 i)
  have he := ConcreteCategory.congr_hom h (ULift.up ((zeroProductIso k).hom ≫ α))
  change (toReducedTorus k 2).hom.app (op (Cor.simplexProduct (point k) 0))
    (ULift.up (((zeroProductIso k).hom ≫ α) ≫
      (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 1 i))) = 0 at he
  change singularClass k ((toReducedTorus k 2).hom.app
    (op (Cor.simplexProduct (point k) 0))
      (ULift.up ((zeroProductIso k).hom ≫ α ≫
        (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 1 i)))) = 0
  rw [Category.assoc] at he
  rw [he, map_zero]

/-- The rational point with its two specified unit coordinates. -/
def rationalPair (a b : kˣ) : SmoothSite.base (Spec (.of k)) ⟶
    SmoothSite.torusPower (.of k) 2 :=
  SmoothSite.torusPowerLift (.of k) 2 ![rationalTorusPoint k a, rationalTorusPoint k b]

/-- Append a fixed unit to the genuine one-fold torus. -/
def appendUnit (b : kˣ) : SmoothSite.torusPower (.of k) 1 ⟶
    SmoothSite.torusPower (.of k) 2 :=
  SmoothSite.torusPowerLift (.of k) 2
    ![SmoothSite.torusCoordinate (.of k) 1 0,
      SmoothSite.torusPowerToBase (.of k) 1 ≫ rationalTorusPoint k b]

/-- Prepend a fixed unit to the genuine one-fold torus. -/
def prependUnit (a : kˣ) : SmoothSite.torusPower (.of k) 1 ⟶
    SmoothSite.torusPower (.of k) 2 :=
  SmoothSite.torusPowerLift (.of k) 2
    ![SmoothSite.torusPowerToBase (.of k) 1 ≫ rationalTorusPoint k a,
      SmoothSite.torusCoordinate (.of k) 1 0]

@[reassoc (attr := simp)]
theorem rationalPoint_toBase (a : kˣ) :
    rationalPoint k a ≫ SmoothSite.torusPowerToBase (.of k) 1 = 𝟙 _ := by
  apply SmoothSite.torusPower_hom_ext (.of k) 0
  intro i
  exact Fin.elim0 i

/-- Appending a constant coordinate preserves the literal rational graph. -/
@[reassoc (attr := simp)]
theorem rationalPoint_appendUnit (a b : kˣ) :
    rationalPoint k a ≫ appendUnit k b = rationalPair k a b := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  rw [Category.assoc, appendUnit, rationalPair, SmoothSite.torusPowerLift_coordinate,
    SmoothSite.torusPowerLift_coordinate]
  fin_cases i
  · change rationalPoint k a ≫ SmoothSite.torusCoordinate (.of k) 1 0 = rationalTorusPoint k a
    exact SmoothSite.torusPowerLift_coordinate (.of k) 1 _ 0
  · change rationalPoint k a ≫ SmoothSite.torusPowerToBase (.of k) 1 ≫
      rationalTorusPoint k b = rationalTorusPoint k b
    rw [rationalPoint_toBase_assoc]

/-- Prepending a constant coordinate preserves the literal rational graph. -/
@[reassoc (attr := simp)]
theorem rationalPoint_prependUnit (a b : kˣ) :
    rationalPoint k b ≫ prependUnit k a = rationalPair k a b := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  rw [Category.assoc, prependUnit, rationalPair, SmoothSite.torusPowerLift_coordinate,
    SmoothSite.torusPowerLift_coordinate]
  fin_cases i
  · change rationalPoint k b ≫ SmoothSite.torusPowerToBase (.of k) 1 ≫
      rationalTorusPoint k a = rationalTorusPoint k a
    rw [rationalPoint_toBase_assoc]
  · change rationalPoint k b ≫ SmoothSite.torusCoordinate (.of k) 1 0 = rationalTorusPoint k b
    exact SmoothSite.torusPowerLift_coordinate (.of k) 1 _ 0

/-- The genuine raw homology class of the rational two-coordinate graph. -/
def graphSymbol (a b : kˣ) : (motivicRawBaseComplex k 2).homology 2 :=
  cycleClass k ((Cor.graphFunctor k).map (rationalPair k a b))

/-- Evaluation at the identity unit is the actual torus identity section. -/
@[simp] theorem rationalTorusPoint_one : rationalTorusPoint k 1 = SmoothSite.torusOne (.of k) := by
  apply MorphismProperty.Over.Hom.ext
  rfl

/-- The left identity-coordinate rational point factors through its actual axis. -/
theorem rationalPair_one_left (b : kˣ) :
    rationalPair k 1 b = rationalPoint k b ≫ SmoothSite.torusInsertOne (.of k) 1 0 := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  fin_cases i
  · change rationalPair k 1 b ≫ SmoothSite.torusCoordinate (.of k) 2 0 =
      (rationalPoint k b ≫ SmoothSite.torusInsertOne (.of k) 1 0) ≫
        SmoothSite.torusCoordinate (.of k) 2 0
    rw [rationalPair, SmoothSite.torusPowerLift_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_self, rationalPoint_toBase_assoc]
    exact rationalTorusPoint_one k
  · change rationalPair k 1 b ≫ SmoothSite.torusCoordinate (.of k) 2
      ((0 : Fin 2).succAbove (0 : Fin 1)) =
      (rationalPoint k b ≫ SmoothSite.torusInsertOne (.of k) 1 0) ≫
        SmoothSite.torusCoordinate (.of k) 2 ((0 : Fin 2).succAbove (0 : Fin 1))
    rw [rationalPair, SmoothSite.torusPowerLift_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_succAbove]
    change rationalTorusPoint k b = rationalPoint k b ≫ SmoothSite.torusCoordinate (.of k) 1 0
    exact (SmoothSite.torusPowerLift_coordinate (.of k) 1 (fun _ => rationalTorusPoint k b) 0).symm

/-- The right identity-coordinate rational point factors through its actual axis. -/
theorem rationalPair_one_right (a : kˣ) :
    rationalPair k a 1 = rationalPoint k a ≫ SmoothSite.torusInsertOne (.of k) 1 1 := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  fin_cases i
  · change rationalPair k a 1 ≫ SmoothSite.torusCoordinate (.of k) 2
      ((1 : Fin 2).succAbove (0 : Fin 1)) =
      (rationalPoint k a ≫ SmoothSite.torusInsertOne (.of k) 1 1) ≫
        SmoothSite.torusCoordinate (.of k) 2 ((1 : Fin 2).succAbove (0 : Fin 1))
    rw [rationalPair, SmoothSite.torusPowerLift_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_succAbove]
    change rationalTorusPoint k a = rationalPoint k a ≫ SmoothSite.torusCoordinate (.of k) 1 0
    exact (SmoothSite.torusPowerLift_coordinate (.of k) 1 (fun _ => rationalTorusPoint k a) 0).symm
  · change rationalPair k a 1 ≫ SmoothSite.torusCoordinate (.of k) 2 1 =
      (rationalPoint k a ≫ SmoothSite.torusInsertOne (.of k) 1 1) ≫
        SmoothSite.torusCoordinate (.of k) 2 1
    rw [rationalPair, SmoothSite.torusPowerLift_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_self, rationalPoint_toBase_assoc]
    exact rationalTorusPoint_one k

/-- The actual reduced quotient kills the symbol with left identity coordinate. -/
@[simp] theorem graphSymbol_one_left (b : kˣ) : graphSymbol k 1 b = 0 := by
  rw [graphSymbol, rationalPair_one_left, Functor.map_comp]
  exact cycleClass_axis k 0 _

/-- The actual reduced quotient kills the symbol with right identity coordinate. -/
@[simp] theorem graphSymbol_one_right (a : kˣ) : graphSymbol k a 1 = 0 := by
  rw [graphSymbol, rationalPair_one_right, Functor.map_comp]
  exact cycleClass_axis k 1 _

/-- The complete quadratic endpoint relation survives arbitrary target graph postcomposition. -/
theorem cycleClass_quadratic_postcompose (a b : kˣ)
    (ψ : SmoothSite.torusPower (.of k) 1 ⟶ SmoothSite.torusPower (.of k) 2) :
    cycleClass k ((Cor.graphFunctor k).map (rationalPoint k a ≫ ψ)) +
      cycleClass k ((Cor.graphFunctor k).map (rationalPoint k b ≫ ψ)) =
    cycleClass k ((Cor.graphFunctor k).map (rationalPoint k (a * b) ≫ ψ)) +
      cycleClass k ((Cor.graphFunctor k).map (rationalPoint k 1 ≫ ψ)) := by
  let p : k[X] := (X - C (a : k)) * (X - C (b : k))
  have hd : 1 ≤ p.natDegree := by rw [twoLinear_natDegree]; decide
  let α := singularCorrespondence (twoLinear_monic a b) hd (twoLinear_coeff_zero_ne_zero a b)
  let γ := (Cor.graphFunctor k).map ψ
  have h := cycleClass_endpoints k (α ≫ γ)
  have h0 := congrArg (fun β => β ≫ γ)
    (singularCorrespondence_face_zero (twoLinear_monic a b) hd
      (twoLinear_coeff_zero_ne_zero a b))
  have h1 := congrArg (fun β => β ≫ γ)
    (singularCorrespondence_face_one (twoLinear_monic a b) hd
      (twoLinear_coeff_zero_ne_zero a b))
  dsimp only [α] at h
  simp only [Category.assoc] at h0 h1 h
  rw [h0, h1, polynomialCycle_twoLinear,
    polynomialCycle_target p hd (twoLinear_coeff_zero_ne_zero a b)] at h
  have hu : Units.mk0 (Polynomial.MonicUnitInterpolation.normValue p)
      (Polynomial.MonicUnitInterpolation.normValue_ne_zero p
        (twoLinear_coeff_zero_ne_zero a b)) = a * b := by
    apply Units.ext
    exact twoLinear_normValue a b
  rw [hu] at h
  simpa only [p, twoLinear_natDegree, Nat.reduceSub, Nat.cast_one, one_zsmul,
    Preadditive.add_comp, map_add, γ, ← Functor.map_comp] using h

/-- Multiplication in the first unit is addition of genuine weight-two graph classes. -/
theorem graphSymbol_mul_left (a b c : kˣ) :
    graphSymbol k (a * b) c = graphSymbol k a c + graphSymbol k b c := by
  have h := cycleClass_quadratic_postcompose k a b (appendUnit k c)
  simp only [rationalPoint_appendUnit] at h
  change graphSymbol k a c + graphSymbol k b c =
    graphSymbol k (a * b) c + graphSymbol k 1 c at h
  simpa only [graphSymbol_one_left, add_zero] using h.symm

/-- Multiplication in the second unit is addition of genuine weight-two graph classes. -/
theorem graphSymbol_mul_right (a b c : kˣ) :
    graphSymbol k a (b * c) = graphSymbol k a b + graphSymbol k a c := by
  have h := cycleClass_quadratic_postcompose k b c (prependUnit k a)
  simp only [rationalPoint_prependUnit] at h
  change graphSymbol k a b + graphSymbol k a c =
    graphSymbol k a (b * c) + graphSymbol k a 1 at h
  simpa only [graphSymbol_one_right, add_zero] using h.symm

/-- For a fixed first unit, the original symbol is additive in the second unit group. -/
def graphSymbolRightHom (a : kˣ) : Additive kˣ →+
    (motivicRawBaseComplex k 2).homology 2 where
  toFun b := graphSymbol k a b.toMul
  map_zero' := graphSymbol_one_right k a
  map_add' b c := graphSymbol_mul_right k a b.toMul c.toMul

/-- The original rational graph symbol is additive in both additive unit groups. -/
def graphSymbolHom : Additive kˣ →+ Additive kˣ →+
    (motivicRawBaseComplex k 2).homology 2 where
  toFun a := graphSymbolRightHom k a.toMul
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    exact graphSymbol_one_left k b.toMul
  map_add' a b := by
    apply AddMonoidHom.ext
    intro c
    exact graphSymbol_mul_left k a.toMul b.toMul c.toMul

/-- The bilinear rational-point symbol on the actual integral tensor product. -/
def tensorSymbol : (Additive kˣ ⊗[ℤ] Additive kˣ) →+
    (motivicRawBaseComplex k 2).homology 2 :=
  TensorProduct.liftAddHom (graphSymbolHom k) (by
    intro n a b
    rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul])

/-- The tensor generator is exactly the original rational graph class. -/
@[simp] theorem tensorSymbol_tmul (a b : Additive kˣ) :
    tensorSymbol k (a ⊗ₜ[ℤ] b) = graphSymbol k a.toMul b.toMul := rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Bilinear rational-point symbols in the originally defined derived motivic group. -/
def motivicTensorSymbol : (Additive kˣ ⊗[ℤ] Additive kˣ) →+
    motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k 2 2).symm.toAddMonoidHom.comp (tensorSymbol k)

/-- The derived symbol retains the original graph and positive weight-two convention. -/
theorem motivicTensorSymbol_tmul_comparison (a b : kˣ) :
    motivicRawBaseEvaluationComparison k 2 2
      (motivicTensorSymbol k (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) =
      graphSymbol k a b := by
  change motivicRawBaseEvaluationComparison k 2 2
    ((motivicRawBaseEvaluationComparison k 2 2).symm
      (tensorSymbol k (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b))) = _
  rw [AddEquiv.apply_symm_apply, tensorSymbol_tmul]
  rfl


end Motivic.WeightTwoSymbols
