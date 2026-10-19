/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.BranchTransport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.ResidueDegree
public import Motivic.Aglib.RingTheory.LocalLength.FieldExtensionBaseChangeLength

/-!
# Degree-length balance on the actual exterior generic fiber

For the actual Cartesian base change of a finite map between reduced integral
point closures, every source generic point above a target generic point contributes
its whole-source-stalk multiplicity times the actual base-changed residue degree.
The sum is the original ambient residue degree times the whole-target-stalk
multiplicity. The target generic point must project to the original image generic.

The algebra is the entire tensor of the actual target stalk with the original
source residue field over the original target residue field. Its maximal ideals
are reindexed by the actual generic source fiber. The quotient/residue comparison
preserves the original whole-stalk action before the accepted algebraic balance
is applied. Neither flatness of the base change, reducedness of its whole target,
separability, a single branch, nor constancy of the new residue degrees is assumed.

This is only a coefficient identity above a target generic point. It does not
assert that all source generic points map to target generic points or identify
global fundamental cycles under arbitrary base change.

SOURCE-ONLY: the residue-tensor consumer and branch-transport prerequisite have
not yet been accepted, and this module and its consumer have not been compiled.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Cycles.BaseChange.DegreeLength
open _root_.AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ResidueTensor
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.BranchTransport

section ActualFiber

variable {W Z : Scheme.{u}} (a : W ⟶ Z) [IsFinite a]

/-- The actual generic fiber is finite because the entire actual point fiber
of a finite morphism is finite. No supplied enumeration or branch choice is used. -/
abbrev actualGenericFiberFintype (y : Z) :
    Fintype {w : genericPoints W // a w.1 = y} := by
  have hfinite := a.finite_preimage_singleton y
  change Set.Finite {w : W | a w = y} at hfinite
  letI : Finite {w : W // a w = y} := hfinite.to_subtype
  letI : Finite {w : genericPoints W // a w.1 = y} :=
    Finite.of_injective
      (fun w : {w : genericPoints W // a w.1 = y} => (⟨w.1.1, w.2⟩ : {w : W // a w = y}))
      (by
        intro _ _ h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : {w : W // a w = y} => z.1) h)
  exact Fintype.ofFinite _

/-- Every actual generic source point over the specified target contributes its
own whole-stalk multiplicity and its own actual scheme residue degree. -/
def actualGenericFiberDegreeLengthSum (y : Z) : ℤ :=
  letI := actualGenericFiberFintype a y
  ∑ w : {w : genericPoints W // a w.1 = y},
    (genericMultiplicity w.1 : ℤ) * (a.residueDegree w.1.1 : ℤ)

omit [IsFinite a] in
/-- Aligning the equal target point does not change the actual residue degree. -/
theorem actualFiberResidueMap_finrank {V : Z.Opens} (y : V)
    (w : {w : W // a w = y.1}) :
    letI := (actualFiberResidueMap a y w).hom.toAlgebra
    Module.finrank (Z.residueField y.1) (W.residueField w.1) = a.residueDegree w.1 := by
  rcases y with ⟨y, hy⟩
  rcases w with ⟨w, hw⟩
  dsimp only at hw
  subst y
  rfl

end ActualFiber

section ActualCartesianCharts

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
  {U : (pointClosure (f x)).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)
  {X' Y' : Scheme.{u}} {i : X' ⟶ (pointClosure x).val.subscheme}
  {f' : X' ⟶ Y'} {g : Y' ⟶ (pointClosure (f x)).val.subscheme}
  (sq : IsPullback i f' (pointClosureMap f x) g)
  {V : Y'.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
  (y : V) (hy : g y.1 = genericPoint (pointClosure (f x)).val.subscheme)

local notation "R" => Y'.presheaf.stalk (Subtype.val y)
local notation "L" => Y.residueField (f x)
local notation "M" => X.residueField x

/-- The original source residue field carries the actual finite-map residue action. -/
local instance degreeLengthOriginalResidueAlgebra : Algebra L M :=
  originalResidueAlgebra f x

local instance degreeLength_originalResidueFinite : Module.Finite L M :=
  residueFieldMap_finite f x

local notation "T" => R ⊗[L] M

attribute [local instance] Ideal.Quotient.field

/-- The literal maximal quotient of the entire tensor is the actual source
residue field, through the canonical quotient and the constructed branch stalk. -/
def tensorBranchQuotientEquiv :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    (T ⧸ q.asIdeal) ≃+*
      X'.residueField (tensorFiberEquiv f x hU sq hV hVU y hy q).1 := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  exact (Module.finiteAlgebraResidueQuotientEquiv T q).toRingEquiv.trans
    (tensorBranchResidueEquiv f x hU sq hV hVU y hy q)

/-- The quotient comparison retains the full target-stalk action, followed by
the actual aligned scheme residue map. In particular no target residue field
has been substituted for the whole target stalk in the tensor algebra. -/
theorem tensorBranchQuotientEquiv_scalarSquare :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    (tensorBranchQuotientEquiv f x hU sq hV hVU y hy q).toRingHom.comp
        (algebraMap R (T ⧸ q.asIdeal)) =
      (actualFiberResidueMap f' y (tensorFiberEquiv f x hU sq hV hVU y hy q)).hom.comp
        (Y'.residue y.1).hom := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  ext r
  simp only [tensorBranchQuotientEquiv, id, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv]
  rw [IsScalarTower.algebraMap_apply R T (T ⧸ q.asIdeal),
    (Module.finiteAlgebraResidueQuotientEquiv T q).commutes]
  change tensorBranchResidueEquiv f x hU sq hV hVU y hy q
      (IsLocalRing.residue _ (tensorBranchBaseMap f x hU y hy q r)) = _
  rw [← tensorBranchResidueMap_residue f x hU sq hV hVU y hy q r]
  exact RingHom.congr_fun
    (tensorBranchResidueEquiv_scalarSquare f x hU sq hV hVU y hy q) (Y'.residue y.1 r)

/-- Every algebraic residue weight is the actual base-changed scheme residue
degree of that branch, proved using the whole-target-stalk scalar square. -/
theorem tensorBranch_residueDegree :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    Module.finiteAlgebraResidueDegree R T q =
      f'.residueDegree (tensorFiberEquiv f x hU sq hV hVU y hy q).1 := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  let w := tensorFiberEquiv f x hU sq hV hVU y hy q
  let : Algebra (IsLocalRing.ResidueField R) (X'.residueField w.1) :=
    (actualFiberResidueMap f' y w).hom.toAlgebra
  let : Algebra R (X'.residueField w.1) :=
    ((actualFiberResidueMap f' y w).hom.comp (Y'.residue y.1).hom).toAlgebra
  let : IsScalarTower R (IsLocalRing.ResidueField R) (X'.residueField w.1) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact (Module.fieldExtensionBaseChange_residueDegree_eq_of_square L M R q
    (tensorBranchQuotientEquiv f x hU sq hV hVU y hy q)
    (tensorBranchQuotientEquiv_scalarSquare f x hU sq hV hVU y hy q)).trans
      (actualFiberResidueMap_finrank f' y w)

/-- The branch length is the length of the entire actual source stalk. -/
theorem tensorBranch_length :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) =
      Module.length
        (X'.presheaf.stalk (tensorFiberEquiv f x hU sq hV hVU y hy q).1)
        (X'.presheaf.stalk (tensorFiberEquiv f x hU sq hV hVU y hy q).1) := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  exact ringLength_eq_of_ringEquiv (tensorBranchStalkEquiv f x hU sq hV hVU y hy q)

/-- The same whole-source length gives the actual generic multiplicity after
reindexing to the actual generic source fiber. -/
theorem tensorBranch_genericMultiplicity (hygen : y.1 ∈ genericPoints Y') :
    let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
    ∀ (q : MaximalSpectrum T),
    (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat =
      genericMultiplicity (tensorGenericFiberEquiv f x hU sq hV hVU y hy hygen q).1 := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  dsimp only
  intro q
  exact congrArg ENat.toNat (tensorBranch_length f x hU sq hV hVU y hy q)

variable [IsLocallyNoetherian Y']

include hU sq hV hVU hy in
/-- Integer conversion loses no infinite length at any actual generic source
branch. Finiteness is derived from the whole Artinian target and its finite tensor. -/
theorem actualGenericFiber_length_ne_top (hygen : y.1 ∈ genericPoints Y')
    (w : {w : genericPoints X' // f' w.1 = y.1}) :
    Module.length (X'.presheaf.stalk w.1.1) (X'.presheaf.stalk w.1.1) ≠ ⊤ := by
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let : IsArtinianRing R :=
    isArtinianRing_stalk_of_mem_genericPoints y.1 hygen
  obtain ⟨q, rfl⟩ := (tensorGenericFiberEquiv f x hU sq hV hVU y hy hygen).surjective w
  change Module.length
    (X'.presheaf.stalk (tensorFiberEquiv f x hU sq hV hVU y hy q).1)
    (X'.presheaf.stalk (tensorFiberEquiv f x hU sq hV hVU y hy q).1) ≠ ⊤
  rw [← tensorBranch_length f x hU sq hV hVU y hy q]
  exact Module.fieldExtensionBaseChange_localLength_ne_top L M R q

include hU hV hVU hy in
/-- On actual affine neighborhoods, the accepted whole-Artinian-tensor balance
reindexes to the complete actual generic fiber, retaining all colliding branches. -/
theorem actualGenericFiberDegreeLengthSum_eq_of_charts (hygen : y.1 ∈ genericPoints Y') :
    letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
    actualGenericFiberDegreeLengthSum f' y.1 =
      (f.residueDegree x : ℤ) * (genericMultiplicity (⟨y.1, hygen⟩ : genericPoints Y') : ℤ) := by
  classical
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  let := (originalResidueToStalk f x hU g y.1 hy).toAlgebra
  let : IsArtinianRing R :=
    isArtinianRing_stalk_of_mem_genericPoints y.1 hygen
  let : Finite (MaximalSpectrum T) :=
    Module.finiteAlgebra_maximalSpectrum_finite R T
  let : Fintype (MaximalSpectrum T) := Fintype.ofFinite _
  let := actualGenericFiberFintype f' y.1
  change (∑ w : {w : genericPoints X' // f' w.1 = y.1},
    (genericMultiplicity w.1 : ℤ) * (f'.residueDegree w.1.1 : ℤ)) = _
  calc
    _ = ∑ q : MaximalSpectrum T,
        ((Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat : ℤ) *
            (Module.finiteAlgebraResidueDegree R T q : ℤ) := by
      symm
      apply Fintype.sum_equiv (tensorGenericFiberEquiv f x hU sq hV hVU y hy hygen)
      intro q
      rw [tensorBranch_genericMultiplicity f x hU sq hV hVU y hy hygen q,
        tensorBranch_residueDegree f x hU sq hV hVU y hy q]
      rfl
    _ = _ := Module.fieldExtensionBaseChange_sum_integerLength_mul_residueDegree L M R

end ActualCartesianCharts

section ActualCartesian

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
  {X' Y' : Scheme.{u}} {i : X' ⟶ (pointClosure x).val.subscheme}
  {f' : X' ⟶ Y'} {g : Y' ⟶ (pointClosure (f x)).val.subscheme}
  (sq : IsPullback i f' (pointClosureMap f x) g) [IsLocallyNoetherian Y']

/-- The chart-free all-branch coefficient formula for the ACTUAL Cartesian
base change of the ACTUAL finite point-closure map. Only the selected target
generic point is required to project to the original image generic point. -/
theorem actualGenericFiberDegreeLengthSum_eq (y : genericPoints Y')
    (hy : g y.1 = genericPoint (pointClosure (f x)).val.subscheme) :
    letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
    actualGenericFiberDegreeLengthSum f' y.1 =
      (f.residueDegree x : ℤ) * (genericMultiplicity y : ℤ) := by
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, _⟩ :=
    (pointClosure (f x)).val.subscheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show genericPoint (pointClosure (f x)).val.subscheme ∈
        (⊤ : (pointClosure (f x)).val.subscheme.Opens) from trivial)
      (⊤ : (pointClosure (f x)).val.subscheme.Opens).isOpen
  let : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hyU : y.1 ∈ g ⁻¹ᵁ U := by
    change g y.1 ∈ U
    rw [hy]
    exact hηU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hyU (g ⁻¹ᵁ U).isOpen
  exact actualGenericFiberDegreeLengthSum_eq_of_charts f x hU sq hV hVU ⟨y.1, hyV⟩ hy y.2

/-- A signed coefficient of the original point closure weights the entire
actual generic fiber. Negative coefficients and cancellations are retained. -/
theorem actualGenericFiberDegreeLengthSum_smul (y : genericPoints Y')
    (hy : g y.1 = genericPoint (pointClosure (f x)).val.subscheme) (c : ℤ) :
    letI : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
    c * actualGenericFiberDegreeLengthSum f' y.1 =
      (c * (f.residueDegree x : ℤ)) * (genericMultiplicity y : ℤ) := by
  let : IsFinite f' := MorphismProperty.of_isPullback sq inferInstance
  rw [actualGenericFiberDegreeLengthSum_eq f x sq y hy, mul_assoc]

end ActualCartesian

end AlgebraicGeometry.Scheme.Cycles.BaseChange.DegreeLength
