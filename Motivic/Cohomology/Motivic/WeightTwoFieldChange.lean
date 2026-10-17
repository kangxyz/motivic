/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneCohomologyFieldChange
public import Motivic.Cohomology.Motivic.WeightTwoFiniteSymbols
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Field change of the original weight-two rational symbols

The actual signed cycle field-change map preserves the literal two-coordinate
rational graph. Consequently the original tensor symbol commutes with actual
integral motivic field change, and its original coefficient reduction commutes
with finite field change at every level. The tensor factors use the ordinary
map on units. No Steinberg relation or Milnor K-theory comparison is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct Simplicial

universe w u

namespace Motivic.WeightTwoFieldChange

open PresheafWithTransfers WeightOnePointNorm WeightOneBoundaryNorm
open WeightTwoSymbols WeightTwoFiniteSymbols

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Laurent evaluation at the ordinary image unit respects coefficient change. -/
theorem rationalTorusPoint_coefficient (a : kˣ) :
    (rationalTorusPoint L (Units.map φ.toMonoidHom a)).left ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ (rationalTorusPoint k a).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change LaurentPolynomial.eval₂ (RingHom.id L) (Units.map φ.toMonoidHom a)
      (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)
        (LaurentPolynomial.C r)) = φ (LaurentPolynomial.eval₂ (RingHom.id k) a
          (LaurentPolynomial.C r))
    rw [CommRingCat.PolynomialLaurent.laurentMap_C]
    simp only [LaurentPolynomial.eval₂_C, RingHom.id_apply]
    rfl
  · change LaurentPolynomial.eval₂ (RingHom.id L) (Units.map φ.toMonoidHom a)
      (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)
        (LaurentPolynomial.T 1)) = φ (LaurentPolynomial.eval₂ (RingHom.id k) a
          (LaurentPolynomial.T 1))
    rw [CommRingCat.PolynomialLaurent.laurentMap_T]
    simp only [LaurentPolynomial.eval₂_T, zpow_one, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]

/-- The original Laurent-evaluation point commutes with the literal pullback comparison. -/
@[reassoc]
theorem rationalTorusPoint_fieldChange (a : kˣ) :
    (SmoothSite.fieldBaseChange φ).map (rationalTorusPoint k a) ≫
        (SmoothSite.torusBaseChangeIso (CommRingCat.ofHom φ)).hom =
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom ≫
        rationalTorusPoint L (Units.map φ.toMonoidHom a) := by
  apply (cancel_mono (SmoothSite.torusBaseChangeIso (CommRingCat.ofHom φ)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · calc
      _ = pullback.fst (𝟙 (Spec (.of k))) (Spec.map (CommRingCat.ofHom φ)) ≫
          (rationalTorusPoint k a).left :=
        SmoothSite.baseChange_map_fst _ (rationalTorusPoint k a)
      _ = (pullback.snd (𝟙 (Spec (.of k))) (Spec.map (CommRingCat.ofHom φ)) ≫
          Spec.map (CommRingCat.ofHom φ)) ≫ (rationalTorusPoint k a).left :=
        congrArg (fun f => f ≫ (rationalTorusPoint k a).left)
          ((Category.comp_id _).symm.trans
            (pullback.condition (f := 𝟙 (Spec (.of k)))
              (g := Spec.map (CommRingCat.ofHom φ))))
      _ = pullback.snd (𝟙 (Spec (.of k))) (Spec.map (CommRingCat.ofHom φ)) ≫
          (rationalTorusPoint L (Units.map φ.toMonoidHom a)).left ≫
            Spec.map (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom φ)) :=
        (Category.assoc _ _ _).trans (congrArg
          (fun f => pullback.snd (𝟙 (Spec (.of k))) (Spec.map (CommRingCat.ofHom φ)) ≫ f)
            (rationalTorusPoint_coefficient φ a).symm)
      _ = _ := Eq.symm ((Category.assoc _ _ _).trans
        (congrArg (fun f => pullback.snd (𝟙 (Spec (.of k)))
            (Spec.map (CommRingCat.ofHom φ)) ≫ f)
          ((Category.assoc _ _ _).trans (congrArg
            (fun f => (rationalTorusPoint L (Units.map φ.toMonoidHom a)).left ≫ f)
              (SmoothSite.torusBaseChangeIso_inv_fst (CommRingCat.ofHom φ))))))
  · exact (MorphismProperty.Over.w
      ((SmoothSite.fieldBaseChange φ).map (rationalTorusPoint k a))).trans
        (MorphismProperty.Over.w
          ((SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom ≫
            rationalTorusPoint L (Units.map φ.toMonoidHom a) ≫
              (SmoothSite.torusBaseChangeIso (CommRingCat.ofHom φ)).inv)).symm

/-- Both coordinates of the original rational pair are the ordinary image units. -/
@[reassoc]
theorem rationalPair_fieldChange (a b : kˣ) :
    (SmoothSite.fieldBaseChange φ).map (rationalPair k a b) ≫
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) 2).hom =
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom ≫
        rationalPair L (Units.map φ.toMonoidHom a) (Units.map φ.toMonoidHom b) := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, SmoothSite.torusPowerBaseChangeIso_coordinate,
    ← Functor.map_comp_assoc]
  simp only [Category.assoc, rationalPair, SmoothSite.torusPowerLift_coordinate]
  fin_cases i <;> exact rationalTorusPoint_fieldChange φ _

/-- The actual signed field-change cycle preserves each original rational graph. -/
theorem rationalGraph_fieldChange (a b : kˣ) :
    baseTorusCycleFieldChange φ 2 ((Cor.graphFunctor k).map (rationalPair k a b)) =
      (Cor.graphFunctor L).map
        (rationalPair L (Units.map φ.toMonoidHom a) (Units.map φ.toMonoidHom b)) := by
  change (Cor.graphFunctor L).map _ ≫
    (Cor.fieldBaseChange φ).map ((Cor.graphFunctor k).map _) ≫
      (Cor.graphFunctor L).map _ = _
  rw [Cor.fieldBaseChange_graph, ← Functor.map_comp, rationalPair_fieldChange,
    Functor.map_comp, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- Taking the original top raw class commutes with the actual cochain map. -/
@[reassoc]
theorem rawClass_fieldChange :
    rawClass k ≫ HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2 =
      (motivicRawBaseComplexMap φ 2).f 2 ≫ rawClass L := by
  have h :
      ((motivicRawBaseComplex k 2).iCyclesIso 2 3 ((ComplexShape.up ℤ).next_eq' rfl)
        (raw_outgoing_d_zero k)).inv ≫
          HomologicalComplex.cyclesMap (motivicRawBaseComplexMap φ 2) 2 =
      (motivicRawBaseComplexMap φ 2).f 2 ≫
        ((motivicRawBaseComplex L 2).iCyclesIso 2 3 ((ComplexShape.up ℤ).next_eq' rfl)
          (raw_outgoing_d_zero L)).inv := by
    apply (cancel_mono ((motivicRawBaseComplex L 2).iCycles 2)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]
  unfold rawClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    h, Category.assoc]

/-- The actual degree-zero singular map passes through the original class map. -/
theorem singularClass_fieldChange
    (s : sections (reducedTorus k 2) (Cor.simplexProduct (point k) 0)) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
        (singularClass k s) =
      singularClass L ((reducedTorusSingularFieldChange φ 2).f 0 s) := by
  change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
    (rawClass k ((motivicRawBaseComplexXIso k 2 0).inv s)) = _
  rw [← ConcreteCategory.comp_apply, rawClass_fieldChange, ConcreteCategory.comp_apply]
  have h := motivicRawBaseComplexMap_f φ 2 0
  change (motivicRawBaseComplexMap φ 2).f 2 = _ at h
  rw [h]
  change rawClass L ((motivicRawBaseComplexXIso L 2 0).inv
    ((reducedTorusSingularFieldChange φ 2).f 0
      ((motivicRawBaseComplexXIso k 2 0).hom
        ((motivicRawBaseComplexXIso k 2 0).inv s)))) = _
  rw [Iso.inv_hom_id_apply]
  rfl

/-- Original point-cycle classes commute with the full signed cycle field change. -/
theorem cycleClass_fieldChange (α : point k ⟶ WeightTwoSymbols.target k) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2 (cycleClass k α) =
      cycleClass L (baseTorusCycleFieldChange φ 2 α) := by
  change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
    (singularClass k ((toReducedTorus k 2).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up ((zeroProductIso k).hom ≫ α)))) = _
  rw [singularClass_fieldChange, reducedTorusSingularFieldChange_quotient,
    singularClass_quotient, Functor.map_comp]
  apply congrArg (cycleClass L)
  simp only [← Category.assoc, WeightOneCohomologyFieldChange.zeroProductIso_fieldChange_inv]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The original raw graph symbol maps to the graph of the ordinary image pair. -/
theorem graphSymbol_fieldChange (a b : kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2 (graphSymbol k a b) =
      graphSymbol L (Units.map φ.toMonoidHom a) (Units.map φ.toMonoidHom b) := by
  unfold graphSymbol
  rw [cycleClass_fieldChange, rationalGraph_fieldChange]

/-- Apply the ordinary field map on units in each original integral tensor factor. -/
def unitsTensorFieldChange : (Additive kˣ ⊗[ℤ] Additive kˣ) →+
    (Additive Lˣ ⊗[ℤ] Additive Lˣ) :=
  (TensorProduct.map (Units.map φ.toMonoidHom).toAdditive.toIntLinearMap
    (Units.map φ.toMonoidHom).toAdditive.toIntLinearMap).toAddMonoidHom

/-- Each pure tensor maps to the pure tensor of the ordinary image units. -/
@[simp]
theorem unitsTensorFieldChange_tmul (a b : kˣ) :
    unitsTensorFieldChange φ (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b) =
      Additive.ofMul (Units.map φ.toMonoidHom a) ⊗ₜ[ℤ]
        Additive.ofMul (Units.map φ.toMonoidHom b) := rfl

/-- The original tensor symbol is natural for the actual signed raw cochain map. -/
theorem tensorSymbol_fieldChange (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2 (tensorSymbol k x) =
      tensorSymbol L (unitsTensorFieldChange φ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
      (graphSymbol k a.toMul b.toMul) =
        graphSymbol L (Units.map φ.toMonoidHom a.toMul) (Units.map φ.toMonoidHom b.toMul)
    exact graphSymbol_fieldChange φ a.toMul b.toMul
  | add x y hx hy => simp only [map_add, hx, hy]

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The original derived graph class maps to the graph of the ordinary image pair. -/
theorem motivicGraphSymbol_fieldChange (a b : kˣ) :
    motivicCohomologyFieldChange φ 2 2
        ((motivicRawBaseEvaluationComparison k 2 2).symm (graphSymbol k a b)) =
      (motivicRawBaseEvaluationComparison L 2 2).symm
        (graphSymbol L (Units.map φ.toMonoidHom a) (Units.map φ.toMonoidHom b)) := by
  apply (motivicRawBaseEvaluationComparison L 2 2).injective
  rw [motivicCohomologyFieldChange_rawComparison, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply, graphSymbol_fieldChange]

/-- The original derived tensor symbol commutes with the actual motivic field map. -/
theorem motivicTensorSymbol_fieldChange (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    motivicCohomologyFieldChange φ 2 2 (motivicTensorSymbol k x) =
      motivicTensorSymbol L (unitsTensorFieldChange φ x) := by
  apply (motivicRawBaseEvaluationComparison L 2 2).injective
  rw [motivicCohomologyFieldChange_rawComparison]
  change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
      (motivicRawBaseEvaluationComparison k 2 2
        ((motivicRawBaseEvaluationComparison k 2 2).symm (tensorSymbol k x))) =
    motivicRawBaseEvaluationComparison L 2 2
      ((motivicRawBaseEvaluationComparison L 2 2).symm
        (tensorSymbol L (unitsTensorFieldChange φ x)))
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, tensorSymbol_fieldChange]

/-- The actual integral commuting square holds as an equality of additive maps. -/
theorem motivicTensorSymbol_fieldChange_square :
    (motivicCohomologyFieldChange φ 2 2).comp (motivicTensorSymbol k) =
      (motivicTensorSymbol L).comp (unitsTensorFieldChange φ) :=
  AddMonoidHom.ext (motivicTensorSymbol_fieldChange φ)

/-- Original integral reduction gives finite tensor naturality at every coefficient level. -/
theorem finiteTensorSymbol_fieldChange (n : ℕ) (x : Additive kˣ ⊗[ℤ] Additive kˣ) :
    motivicFiniteCohomologyFieldChange φ 2 2 n (finiteTensorSymbol k n x) =
      finiteTensorSymbol L n (unitsTensorFieldChange φ x) := by
  rw [finiteTensorSymbol_eq_reduction, motivicCohomologyFieldChange_integralReduction,
    motivicTensorSymbol_fieldChange, finiteTensorSymbol_eq_reduction]

/-- The finite commuting square uses the original finite symbol and ordinary tensor map. -/
theorem finiteTensorSymbol_fieldChange_square (n : ℕ) :
    (motivicFiniteCohomologyFieldChange φ 2 2 n).comp (finiteTensorSymbol k n) =
      (finiteTensorSymbol L n).comp (unitsTensorFieldChange φ) :=
  AddMonoidHom.ext (finiteTensorSymbol_fieldChange φ n)

/-- The finite map sends each original reduced graph to the ordinary image graph. -/
theorem finiteTensorSymbol_tmul_fieldChange (n : ℕ) (a b : kˣ) :
    motivicFiniteCohomologyFieldChange φ 2 2 n
        (finiteTensorSymbol k n (Additive.ofMul a ⊗ₜ[ℤ] Additive.ofMul b)) =
      finiteTensorSymbol L n
        (Additive.ofMul (Units.map φ.toMonoidHom a) ⊗ₜ[ℤ]
          Additive.ofMul (Units.map φ.toMonoidHom b)) := by
  rw [finiteTensorSymbol_fieldChange, unitsTensorFieldChange_tmul]

end Motivic.WeightTwoFieldChange
