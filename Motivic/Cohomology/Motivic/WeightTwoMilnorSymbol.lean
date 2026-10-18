/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSteinberg
public import Motivic.Cohomology.Motivic.WeightTwoFieldChange
public import Aglib.KTheory.MilnorK.K2.Map
public import Aglib.KTheory.MilnorK.K2.Symbols

/-!
# The actual motivic Milnor symbol

The original rational graph symbol satisfies bilinearity and the proved
characteristic-zero Steinberg relation. It therefore descends through the
original tensor/Steinberg presentation of Milnor K₂. The actual raw-to-derived
comparison and original coefficient reduction give maps to integral and finite
motivic cohomology. All coefficient levels are allowed. The finite map also
descends through the exact subgroup of multiples in Milnor K₂.

The symbol formulas, tensor factorizations, reduction squares, and field-change
squares retain the original graphs and cohomological maps. No isomorphism,
surjectivity, norm, reciprocity, or comparison with Quillen K-theory is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe w u

namespace Motivic.WeightTwoMilnorSymbol

open MilnorK.K2

variable (k : Type u) [Field k]

/-- The original signed raw field homology in bidegree `(2,2)`. -/
abbrev rawH22 := (motivicRawBaseComplex k 2).homology 2

/-- The literal subgroup of natural multiples in the original Milnor group. -/
def milnorMultiples (n : ℕ) : AddSubgroup (MilnorK.K2.Group k) :=
  (n • AddMonoidHom.id (MilnorK.K2.Group k)).range

/-- Membership means an actual multiplication equation in Milnor K₂. -/
theorem mem_milnorMultiples (n : ℕ) (x : MilnorK.K2.Group k) :
    x ∈ milnorMultiples k n ↔ ∃ y : MilnorK.K2.Group k, n • y = x := Iff.rfl

/-- The original tensor/Steinberg quotient further reduced modulo multiples. -/
abbrev milnorModulo (n : ℕ) := MilnorK.K2.Group k ⧸ milnorMultiples k n

variable [CharZero k]

/-- The original graph symbol, with its established bilinearity and Steinberg proof. -/
def rawSymbolMap : SymbolMap (K := k) (A := rawH22 k) where
  toFun := WeightTwoSymbols.graphSymbol k
  mul_left := WeightTwoSymbols.graphSymbol_mul_left k
  mul_right := WeightTwoSymbols.graphSymbol_mul_right k
  steinberg a b hab := WeightTwoSteinbergBound.graphSymbol_steinberg a b
    (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hab))

/-- Descent of the actual graph classes through the original Milnor presentation. -/
def rawMilnorSymbol : MilnorK.K2.Group k →+ rawH22 k := liftSymbols (rawSymbolMap k)

/-- A literal Milnor symbol is sent to its original rational graph class. -/
@[simp] theorem rawMilnorSymbol_symbol (a b : kˣ) :
    rawMilnorSymbol k (symbol a b) = WeightTwoSymbols.graphSymbol k a b := rfl

/-- The quotient lift factors the original tensor symbol, on every tensor. -/
theorem rawMilnorSymbol_tensor (x : UnitTensor k) :
    rawMilnorSymbol k ((steinbergSpan k).mkQ x) = WeightTwoSymbols.tensorSymbol k x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => exact rawMilnorSymbol_symbol k a.toMul b.toMul
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The raw tensor factorization is an equality of additive maps. -/
theorem rawMilnorSymbol_tensor_square :
    (rawMilnorSymbol k).comp (steinbergSpan k).mkQ.toAddMonoidHom =
      WeightTwoSymbols.tensorSymbol k :=
  AddMonoidHom.ext (rawMilnorSymbol_tensor k)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The originally defined derived motivic cohomology group in bidegree `(2,2)`. -/
abbrev derivedH22 := motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))

/-- The actual derived Milnor symbol, using the original field-evaluation comparison. -/
def motivicMilnorSymbol : MilnorK.K2.Group k →+ derivedH22 k :=
  (motivicRawBaseEvaluationComparison k 2 2).symm.toAddMonoidHom.comp (rawMilnorSymbol k)

/-- The derived symbol is exactly the original graph transported by the actual comparison. -/
@[simp] theorem motivicMilnorSymbol_symbol (a b : kˣ) :
    motivicMilnorSymbol k (symbol a b) =
      (motivicRawBaseEvaluationComparison k 2 2).symm
        (WeightTwoSymbols.graphSymbol k a b) := rfl

/-- The actual comparison sends the derived Milnor map back to its original raw map. -/
theorem motivicMilnorSymbol_comparison (x : MilnorK.K2.Group k) :
    motivicRawBaseEvaluationComparison k 2 2 (motivicMilnorSymbol k x) =
      rawMilnorSymbol k x :=
  (motivicRawBaseEvaluationComparison k 2 2).apply_symm_apply _

/-- The original derived tensor symbol factors through the exact Steinberg quotient. -/
theorem motivicMilnorSymbol_tensor (x : UnitTensor k) :
    motivicMilnorSymbol k ((steinbergSpan k).mkQ x) =
      WeightTwoSymbols.motivicTensorSymbol k x := by
  change (motivicRawBaseEvaluationComparison k 2 2).symm
    (rawMilnorSymbol k ((steinbergSpan k).mkQ x)) = _
  rw [rawMilnorSymbol_tensor]
  rfl

/-- The integral tensor factorization as an equality of additive maps. -/
theorem motivicMilnorSymbol_tensor_square :
    (motivicMilnorSymbol k).comp (steinbergSpan k).mkQ.toAddMonoidHom =
      WeightTwoSymbols.motivicTensorSymbol k :=
  AddMonoidHom.ext (motivicMilnorSymbol_tensor k)

/-- The finite Milnor symbol is the original integral coefficient reduction. -/
def finiteMilnorSymbol (n : ℕ) : MilnorK.K2.Group k →+
    motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k))) :=
  (motivicBaseIntegralReduction k 2 2 n).comp (motivicMilnorSymbol k)

/-- Every finite Milnor symbol is the original reduced graph class. -/
@[simp] theorem finiteMilnorSymbol_symbol (n : ℕ) (a b : kˣ) :
    finiteMilnorSymbol k n (symbol a b) =
      motivicBaseIntegralReduction k 2 2 n
        ((motivicRawBaseEvaluationComparison k 2 2).symm
          (WeightTwoSymbols.graphSymbol k a b)) := by
  change motivicBaseIntegralReduction k 2 2 n (motivicMilnorSymbol k (symbol a b)) = _
  exact congrArg (motivicBaseIntegralReduction k 2 2 n) (motivicMilnorSymbol_symbol k a b)

/-- Coefficient reduction commutes with the actual Milnor symbol maps. -/
theorem finiteMilnorSymbol_reduction_square (n : ℕ) :
    (motivicBaseIntegralReduction k 2 2 n).comp (motivicMilnorSymbol k) =
      finiteMilnorSymbol k n := rfl

/-- The original finite tensor symbol factors through the same exact Milnor quotient. -/
theorem finiteMilnorSymbol_tensor (n : ℕ) (x : UnitTensor k) :
    finiteMilnorSymbol k n ((steinbergSpan k).mkQ x) =
      WeightTwoFiniteSymbols.finiteTensorSymbol k n x := by
  change motivicBaseIntegralReduction k 2 2 n
    (motivicMilnorSymbol k ((steinbergSpan k).mkQ x)) = _
  rw [motivicMilnorSymbol_tensor]
  rfl

/-- The finite tensor factorization holds as an equality of additive maps at every level. -/
theorem finiteMilnorSymbol_tensor_square (n : ℕ) :
    (finiteMilnorSymbol k n).comp (steinbergSpan k).mkQ.toAddMonoidHom =
      WeightTwoFiniteSymbols.finiteTensorSymbol k n :=
  AddMonoidHom.ext (finiteMilnorSymbol_tensor k n)

/-- The actual top-degree comparison retains the original integral Milnor class. -/
theorem finiteMilnorSymbol_topDegree_comparison (n : ℕ) (x : MilnorK.K2.Group k) :
    FieldTopDegree.topDegreeFiniteEquiv k 2 n (finiteMilnorSymbol k n x) =
      (QuotientAddGroup.mk (motivicMilnorSymbol k x) :
        FieldTopDegree.integralModulo k 2 n) :=
  FieldTopDegree.topDegreeFiniteEquiv_integralReduction k 2 n _

/-- All finite Milnor values are annihilated by the coefficient level. -/
theorem nsmul_finiteMilnorSymbol (n : ℕ) (x : MilnorK.K2.Group k) :
    n • finiteMilnorSymbol k n x = 0 := FieldTopDegree.nsmul_eq_zero k 2 n _

/-- Coefficient level one gives the zero map. -/
@[simp] theorem finiteMilnorSymbol_one (x : MilnorK.K2.Group k) : finiteMilnorSymbol k 1 x = 0 := by
  simpa only [one_nsmul] using nsmul_finiteMilnorSymbol k 1 x

/-- The finite map kills the literal subgroup of Milnor multiples. -/
theorem milnorMultiples_le_ker (n : ℕ) :
    milnorMultiples k n ≤ (finiteMilnorSymbol k n).ker := by
  rintro x ⟨y, rfl⟩
  change finiteMilnorSymbol k n (n • y) = 0
  rw [map_nsmul, nsmul_finiteMilnorSymbol]

/-- The actual finite symbol descends to Milnor K₂ modulo its subgroup of multiples. -/
def finiteMilnorSymbolModulo (n : ℕ) : milnorModulo k n →+
    motivicFiniteCohomology k 2 2 n (SmoothSite.base (Spec (.of k))) :=
  QuotientAddGroup.lift (milnorMultiples k n) (finiteMilnorSymbol k n)
    (milnorMultiples_le_ker k n)

/-- Reducing a Milnor class before its finite symbol gives the original finite value. -/
@[simp] theorem finiteMilnorSymbolModulo_mk (n : ℕ) (x : MilnorK.K2.Group k) :
    finiteMilnorSymbolModulo k n (QuotientAddGroup.mk x) = finiteMilnorSymbol k n x := rfl

/-- The modulo-`n` symbol retains the literal original rational graph. -/
theorem finiteMilnorSymbolModulo_symbol (n : ℕ) (a b : kˣ) :
    finiteMilnorSymbolModulo k n (QuotientAddGroup.mk (symbol a b)) =
      motivicBaseIntegralReduction k 2 2 n
        ((motivicRawBaseEvaluationComparison k 2 2).symm
          (WeightTwoSymbols.graphSymbol k a b)) :=
  (finiteMilnorSymbolModulo_mk k n (symbol a b)).trans (finiteMilnorSymbol_symbol k n a b)

/-- The reduction square uses exactly the quotient by Milnor multiples. -/
theorem finiteMilnorSymbolModulo_reduction_square (n : ℕ) :
    (finiteMilnorSymbolModulo k n).comp (QuotientAddGroup.mk' (milnorMultiples k n)) =
      (motivicBaseIntegralReduction k 2 2 n).comp (motivicMilnorSymbol k) := rfl

section FieldChange

variable {k L : Type u} [Field k] [Field L] [CharZero k] [CharZero L]
variable (φ : k →+* L)

/-- The raw Milnor map commutes with the actual signed field-change map. -/
theorem rawMilnorSymbol_fieldChange_square :
    (HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2).hom.comp
        (rawMilnorSymbol k) =
      (rawMilnorSymbol L).comp (mapAdd φ) := by
  apply symbolHom_ext
  intro a b
  change HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
      (rawMilnorSymbol k (symbol a b)) = rawMilnorSymbol L (mapAdd φ (symbol a b))
  rw [rawMilnorSymbol_symbol, mapAdd_symbol, rawMilnorSymbol_symbol]
  exact WeightTwoFieldChange.graphSymbol_fieldChange φ a b

/-- Every raw Milnor class is natural for the original cochain field map. -/
theorem rawMilnorSymbol_fieldChange (x : MilnorK.K2.Group k) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 2) 2
        (rawMilnorSymbol k x) = rawMilnorSymbol L (mapAdd φ x) :=
  DFunLike.congr_fun (rawMilnorSymbol_fieldChange_square φ) x

/-- The original Milnor field map preserves the exact subgroup of multiples. -/
def milnorModuloFieldChange (n : ℕ) : milnorModulo k n →+ milnorModulo L n :=
  QuotientAddGroup.map (milnorMultiples k n) (milnorMultiples L n) (mapAdd φ) (by
    rintro x ⟨y, rfl⟩
    exact ⟨mapAdd φ y, (map_nsmul (mapAdd φ) n y).symm⟩)

omit [CharZero k] [CharZero L] in
/-- The field map on the quotient sends an actual coset to its ordinary field image. -/
@[simp] theorem milnorModuloFieldChange_mk (n : ℕ) (x : MilnorK.K2.Group k) :
    milnorModuloFieldChange φ n (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (mapAdd φ x) := rfl

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The actual derived Milnor map commutes with the original cohomological field map. -/
theorem motivicMilnorSymbol_fieldChange_square :
    (motivicCohomologyFieldChange φ 2 2).comp (motivicMilnorSymbol k) =
      (motivicMilnorSymbol L).comp (mapAdd φ) := by
  apply symbolHom_ext
  intro a b
  change motivicCohomologyFieldChange φ 2 2 (motivicMilnorSymbol k (symbol a b)) =
    motivicMilnorSymbol L (mapAdd φ (symbol a b))
  rw [motivicMilnorSymbol_symbol, mapAdd_symbol, motivicMilnorSymbol_symbol]
  exact WeightTwoFieldChange.motivicGraphSymbol_fieldChange φ a b

/-- Naturality holds for every Milnor class, using the original field homomorphism. -/
theorem motivicMilnorSymbol_fieldChange (x : MilnorK.K2.Group k) :
    motivicCohomologyFieldChange φ 2 2 (motivicMilnorSymbol k x) =
      motivicMilnorSymbol L (mapAdd φ x) :=
  DFunLike.congr_fun (motivicMilnorSymbol_fieldChange_square φ) x

/-- Finite Milnor naturality follows through the original integral reduction at every level. -/
theorem finiteMilnorSymbol_fieldChange (n : ℕ) (x : MilnorK.K2.Group k) :
    motivicFiniteCohomologyFieldChange φ 2 2 n (finiteMilnorSymbol k n x) =
      finiteMilnorSymbol L n (mapAdd φ x) := by
  change motivicFiniteCohomologyFieldChange φ 2 2 n
    (motivicBaseIntegralReduction k 2 2 n (motivicMilnorSymbol k x)) = _
  rw [motivicCohomologyFieldChange_integralReduction, motivicMilnorSymbol_fieldChange]
  rfl

/-- The all-level finite naturality square is an equality of actual additive maps. -/
theorem finiteMilnorSymbol_fieldChange_square (n : ℕ) :
    (motivicFiniteCohomologyFieldChange φ 2 2 n).comp (finiteMilnorSymbol k n) =
      (finiteMilnorSymbol L n).comp (mapAdd φ) :=
  AddMonoidHom.ext (finiteMilnorSymbol_fieldChange φ n)

/-- The finite map on Milnor K₂ modulo multiples is natural for field homomorphisms. -/
theorem finiteMilnorSymbolModulo_fieldChange (n : ℕ) (x : milnorModulo k n) :
    motivicFiniteCohomologyFieldChange φ 2 2 n (finiteMilnorSymbolModulo k n x) =
      finiteMilnorSymbolModulo L n (milnorModuloFieldChange φ n x) := by
  refine Quotient.inductionOn x ?_
  intro y
  exact finiteMilnorSymbol_fieldChange φ n y

/-- The modulo-`n` naturality square retains both original field maps. -/
theorem finiteMilnorSymbolModulo_fieldChange_square (n : ℕ) :
    (motivicFiniteCohomologyFieldChange φ 2 2 n).comp (finiteMilnorSymbolModulo k n) =
      (finiteMilnorSymbolModulo L n).comp (milnorModuloFieldChange φ n) :=
  AddMonoidHom.ext (finiteMilnorSymbolModulo_fieldChange φ n)

end FieldChange

end Motivic.WeightTwoMilnorSymbol
