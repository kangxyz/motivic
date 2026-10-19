/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.MilnorSymbol
public import Aglib.KTheory.MilnorK.Map
public import Motivic.Cohomology.WeightTwo.FieldChange

/-!
# Field naturality of the actual all-weight diagonal symbol

The original signed raw field-change cochain map sends each actual rational
tuple to its ordinary field image. Hence the all-weight Milnor symbol commutes
with the original derived field map. The statement uses every field homomorphism
between characteristic-zero fields, with no algebraicity or finiteness assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.DiagonalFieldChange
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.SingularComplex

open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open DiagonalTopDegree
open DiagonalCycleSymbols
open DiagonalMilnorSymbol
open WeightOneBoundaryNorm

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Every coordinate of an actual rational tuple commutes with the original field change. -/
@[reassoc]
theorem rationalTuple_fieldChange (q : ℕ) (a : Fin q → kˣ) :
    (SmoothSite.fieldBaseChange φ).map (rationalTuple k q a) ≫
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom =
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom ≫
        rationalTuple L q (fun i => Units.map φ.toMonoidHom (a i)) := by
  apply SmoothSite.torusPower_hom_ext
  intro i
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, SmoothSite.torusPowerBaseChangeIso_coordinate,
    ← Functor.map_comp_assoc]
  simp only [Category.assoc, rationalTuple, SmoothSite.torusPowerLift_coordinate]
  exact WeightTwoFieldChange.rationalTorusPoint_fieldChange φ (a i)

/-- The signed finite-cycle field map preserves the graph of every original rational tuple. -/
theorem rationalGraph_fieldChange (q : ℕ) (a : Fin q → kˣ) :
    baseTorusCycleFieldChange φ q ((Cor.graphFunctor k).map (rationalTuple k q a)) =
      (Cor.graphFunctor L).map (rationalTuple L q (fun i => Units.map φ.toMonoidHom (a i))) := by
  change (Cor.graphFunctor L).map _ ≫
    (Cor.fieldBaseChange φ).map ((Cor.graphFunctor k).map _) ≫
      (Cor.graphFunctor L).map _ = _
  rw [Cor.fieldBaseChange_graph, ← Functor.map_comp, rationalTuple_fieldChange,
    Functor.map_comp, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The canonical original top raw class is natural for the actual cochain field map. -/
@[reassoc]
theorem rawClass_fieldChange (q : ℕ) :
    rawClass k q ≫ HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q =
      (motivicRawBaseComplexMap φ q).f q ≫ rawClass L q := by
  have h :
      ((motivicRawBaseComplex k q).iCyclesIso q ((q : ℤ) + 1)
        ((ComplexShape.up ℤ).next_eq' (by simp)) (raw_outgoing_d_zero k q)).inv ≫
          HomologicalComplex.cyclesMap (motivicRawBaseComplexMap φ q) q =
      (motivicRawBaseComplexMap φ q).f q ≫
        ((motivicRawBaseComplex L q).iCyclesIso q ((q : ℤ) + 1)
          ((ComplexShape.up ℤ).next_eq' (by simp)) (raw_outgoing_d_zero L q)).inv := by
    apply (cancel_mono ((motivicRawBaseComplex L q).iCycles q)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]
  unfold rawClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    h, Category.assoc]

/-- The top raw term dictionary retains the actual singular field map and degree transport. -/
theorem topTermIso_fieldChange (q : ℕ) :
    (topTermIso k q).inv ≫ (motivicRawBaseComplexMap φ q).f q =
      (reducedTorusSingularFieldChange φ q).f 0 ≫ (topTermIso L q).inv := by
  have h := (HomologicalComplex.XIsoOfEq_inv_naturality (motivicRawBaseComplexMap φ q)
    (Indexing.singularDegree_zero q).symm).symm
  change (eqToIso (congrArg (motivicRawBaseComplex k q).X
      (Indexing.singularDegree_zero q).symm)).inv ≫
        (motivicRawBaseComplexMap φ q).f q =
    (motivicRawBaseComplexMap φ q).f (Indexing.singularDegree q 0) ≫
      (eqToIso (congrArg (motivicRawBaseComplex L q).X
        (Indexing.singularDegree_zero q).symm)).inv at h
  rw [topTermIso, Iso.trans_inv, Category.assoc, h, motivicRawBaseComplexMap_f]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

/-- The literal singular class commutes with the full original field-change cycle map. -/
theorem singularClass_fieldChange (q : ℕ) (s : chains k q 0) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q (singularClass k q s) =
      singularClass L q ((reducedTorusSingularFieldChange φ q).f 0 s) := by
  have h : (topTermIso k q).inv ≫ rawClass k q ≫
      HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q =
    (reducedTorusSingularFieldChange φ q).f 0 ≫ (topTermIso L q).inv ≫ rawClass L q := by
      rw [rawClass_fieldChange, ← Category.assoc, topTermIso_fieldChange, Category.assoc]
  exact ConcreteCategory.congr_hom h s

/-- Every actual signed point-cycle representative commutes with the original field change. -/
theorem cycleClass_fieldChange (q : ℕ) (α : point k ⟶ target k q) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q (cycleClass k q α) =
      cycleClass L q (baseTorusCycleFieldChange φ q α) := by
  change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q
    (singularClass k q ((toReducedTorus k q).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up ((zeroProductIso k).hom ≫ α)))) = _
  rw [singularClass_fieldChange, reducedTorusSingularFieldChange_quotient,
    singularClass_quotient, Functor.map_comp]
  apply congrArg (cycleClass L q)
  simp only [← Category.assoc, WeightOneCohomologyFieldChange.zeroProductIso_fieldChange_inv]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The original diagonal rational symbol maps to the tuple of ordinary image units. -/
theorem graphSymbol_fieldChange (q : ℕ) (a : Fin q → kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q (graphSymbol k q a) =
      graphSymbol L q (fun i => Units.map φ.toMonoidHom (a i)) := by
  unfold graphSymbol
  rw [cycleClass_fieldChange, rationalGraph_fieldChange]

variable [CharZero k] [CharZero L]

/-- The standard all-weight Milnor field map commutes with the original raw symbol. -/
theorem rawSymbol_fieldChange (q : ℕ) (x : MilnorK.K k q) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q (rawSymbol k q x) =
      rawSymbol L q (MilnorK.map q φ x) := by
  have h : (HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q).hom.comp
      (rawSymbol k q) = (rawSymbol L q).comp (MilnorK.map q φ).toAddMonoidHom := by
    apply MilnorK.addHom_ext
    intro a
    change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ q) q
      (rawSymbol k q (MilnorK.symbol a)) = rawSymbol L q (MilnorK.map q φ (MilnorK.symbol a))
    rw [rawSymbol_symbol, MilnorK.map_symbol, rawSymbol_symbol, graphSymbol_fieldChange]
    rfl
  exact DFunLike.congr_fun h x

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The actual derived all-weight Milnor symbol is natural for every field homomorphism. -/
theorem motivicSymbol_fieldChange (q : ℕ) (x : MilnorK.K k q) :
    motivicCohomologyFieldChange φ q q (motivicSymbol k q x) =
      motivicSymbol L q (MilnorK.map q φ x) := by
  apply (motivicRawBaseEvaluationComparison L q q).injective
  rw [motivicCohomologyFieldChange_rawComparison, motivicSymbol_comparison,
    motivicSymbol_comparison, rawSymbol_fieldChange]

/-- Naturality is an equality of the original additive maps on all Milnor classes. -/
theorem motivicSymbol_fieldChange_square (q : ℕ) :
    (motivicCohomologyFieldChange φ q q).comp (motivicSymbol k q) =
      (motivicSymbol L q).comp (MilnorK.map q φ).toAddMonoidHom :=
  AddMonoidHom.ext (motivicSymbol_fieldChange φ q)

end Motivic.DiagonalFieldChange
