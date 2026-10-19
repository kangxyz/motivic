/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.NormFieldChange
public import Motivic.Cohomology.Coefficients.Finite.WeightOne
public import Motivic.Cohomology.SuslinVoevodsky.FieldCohomologyChange

/-!
# The actual weight-one equivalences commute with arbitrary field maps

The original determinant norm, the actual signed cycle cochain map, and the
original degree-zero simplex comparison give the integral commuting square.
The original coefficient reduction then gives its finite analogue, with the
literal map on field units modulo their powers. No finiteness, separability,
or coefficient-invertibility assumption is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe w u

namespace Motivic.WeightOneCohomologyFieldChange
open _root_.AlgebraicGeometry.Scheme

open _root_.AlgebraicSimplex
open _root_.Motivic.PresheafWithTransfers
open WeightOnePointNorm
open WeightOneBoundaryNorm
open WeightOneHomologyNorm WeightOneEquivalence WeightOneFiniteCoefficients
open WeightOneNormFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

private theorem hom_base_ext {K : Type u} [Field K]
    {X : SmoothSite (Spec (.of K))} (f g : X ⟶ SmoothSite.base (Spec (.of K))) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  have hf := MorphismProperty.Over.w f
  have hg := MorphismProperty.Over.w g
  change f.left ≫ 𝟙 _ = _ at hf
  change g.left ≫ 𝟙 _ = _ at hg
  simpa only [Category.comp_id] using hf.trans hg.symm

/-- The original zero-simplex identification respects the literal base comparisons. -/
theorem zeroProductIso_fieldChange_hom :
    (Cor.fieldBaseChange φ).map (zeroProductIso k).hom ≫ (Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom =
      (Cor.graphFunctor L).map (SmoothSite.baseSimplexFieldChangeIso φ ⦋0⦌).hom ≫
        (zeroProductIso L).hom := by
  change (Cor.fieldBaseChange φ).map ((Cor.graphFunctor k).map _) ≫
    (Cor.graphFunctor L).map _ = (Cor.graphFunctor L).map _ ≫ (Cor.graphFunctor L).map _
  rw [Cor.fieldBaseChange_graph, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((Cor.graphFunctor L).map) (hom_base_ext _ _)

/-- The inverse zero-simplex identification uses the same original graph comparisons. -/
theorem zeroProductIso_fieldChange_inv :
    (zeroProductIso L).inv ≫ (Cor.graphFunctor L).map
        (SmoothSite.baseSimplexFieldChangeIso φ ⦋0⦌).inv =
      (Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
          (Cor.fieldBaseChange φ).map (zeroProductIso k).inv := by
  let e := baseProductIso k (smoothSiteObj k 0) ≪≫ zeroSimplexIso k
  change (Cor.graphFunctor L).map _ ≫ (Cor.graphFunctor L).map _ =
    (Cor.graphFunctor L).map _ ≫ (Cor.fieldBaseChange φ).map ((Cor.graphFunctor k).map e.inv)
  rw [Cor.fieldBaseChange_graph, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg ((Cor.graphFunctor L).map)
  apply (cancel_mono ((SmoothSite.fieldBaseChange φ).map e.hom)).mp
  apply (cancel_mono (SmoothSite.baseChangeBaseIso
    (Spec.map (CommRingCat.ofHom φ))).hom).mp
  exact hom_base_ext _ _

/-- The original singular degree-zero norm commutes with the entire signed cycle map. -/
theorem degreeZeroNorm_fieldChange
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (point k) 0)) :
    degreeZeroNorm L ((reducedTorusSingularFieldChange φ 1).f 0 s) =
      unitsFieldChange φ (degreeZeroNorm k s) := by
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k 1
    (Cor.simplexProduct (point k) 0) s
  rw [reducedTorusSingularFieldChange_quotient, degreeZeroNorm_quotient,
    degreeZeroNorm_quotient]
  have h := cycleNorm_conjugated_fieldBaseChange φ ((zeroProductIso k).inv ≫ α)
  rw [Functor.map_comp] at h
  simpa only [← Category.assoc, zeroProductIso_fieldChange_inv] using h

/-- The actual top raw norm retains the original signed-shift term dictionary. -/
theorem rawDegreeZeroNorm_fieldChange (x : (motivicRawBaseComplex k 1).X 1) :
    rawDegreeZeroNorm L ((motivicRawBaseComplexMap φ 1).f 1 x) =
      unitsFieldChange φ (rawDegreeZeroNorm k x) := by
  have h := motivicRawBaseComplexMap_f φ 1 0
  change (motivicRawBaseComplexMap φ 1).f 1 = _ at h
  rw [h]
  change degreeZeroNorm L ((motivicRawBaseComplexXIso L 1 0).hom
    ((motivicRawBaseComplexXIso L 1 0).inv
      ((reducedTorusSingularFieldChange φ 1).f 0
        ((motivicRawBaseComplexXIso k 1 0).hom x)))) = _
  rw [Iso.inv_hom_id_apply]
  exact degreeZeroNorm_fieldChange φ _

/-- Taking the genuine raw homology class commutes with the actual cochain map. -/
@[reassoc]
theorem rawClass_fieldChange :
    rawClass k ≫ HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 1) 1 =
      (motivicRawBaseComplexMap φ 1).f 1 ≫ rawClass L := by
  have h :
      ((motivicRawBaseComplex k 1).iCyclesIso 1 2 ((ComplexShape.up ℤ).next_eq' rfl)
        (raw_outgoing_d_zero k)).inv ≫
          HomologicalComplex.cyclesMap (motivicRawBaseComplexMap φ 1) 1 =
      (motivicRawBaseComplexMap φ 1).f 1 ≫
        ((motivicRawBaseComplex L 1).iCyclesIso 1 2 ((ComplexShape.up ℤ).next_eq' rfl)
          (raw_outgoing_d_zero L)).inv := by
    apply (cancel_mono ((motivicRawBaseComplex L 1).iCycles 1)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id_assoc,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]
  unfold rawClass
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    h, Category.assoc]

/-- The actual raw homology norm is natural for every field homomorphism. -/
theorem homologyNorm_fieldChange (x : (motivicRawBaseComplex k 1).homology 1) :
    homologyNorm L (HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 1) 1 x) =
      unitsFieldChange φ (homologyNorm k x) := by
  obtain ⟨y, rfl⟩ := rawClass_surjective k x
  rw [← ConcreteCategory.comp_apply, rawClass_fieldChange, ConcreteCategory.comp_apply,
    homologyNorm_rawClass, homologyNorm_rawClass, rawDegreeZeroNorm_fieldChange]

/-- The induced map sends the original graph class to the graph of the ordinary image unit. -/
theorem graphUnitClass_fieldChange (a : kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 1) 1 (graphUnitClass k a) =
      graphUnitClass L (Units.map φ.toMonoidHom a) := by
  apply homologyNorm_injective L
  rw [homologyNorm_fieldChange, homologyNorm_graphUnitClass, homologyNorm_graphUnitClass]
  rfl

/-- Powers map to the same powers under the original map on field units. -/
theorem powerSubgroup_le_comap (n : ℕ) :
    powerSubgroup k n ≤ (powerSubgroup L n).comap (Units.map φ.toMonoidHom) := by
  rintro a ⟨b, rfl⟩
  exact ⟨Units.map φ.toMonoidHom b, (map_pow (Units.map φ.toMonoidHom) b n).symm⟩

/-- The literal induced multiplicative map on units modulo powers. -/
def unitsModuloPowersFieldChange (n : ℕ) :
    unitsModuloPowers k n →* unitsModuloPowers L n :=
  QuotientGroup.map (powerSubgroup k n) (powerSubgroup L n)
    (Units.map φ.toMonoidHom) (powerSubgroup_le_comap φ n)

/-- A unit coset maps to the coset of its ordinary scalar image, with no inverse twist. -/
@[simp]
theorem unitsModuloPowersFieldChange_mk (n : ℕ) (a : kˣ) :
    unitsModuloPowersFieldChange φ n (QuotientGroup.mk a) =
      (QuotientGroup.mk (Units.map φ.toMonoidHom a) : unitsModuloPowers L n) := rfl

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The original derived geometric norm commutes with the actual integral field map. -/
theorem motivicNorm_fieldChange
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    motivicNorm L (motivicCohomologyFieldChange φ 1 1 x) =
      unitsFieldChange φ (motivicNorm k x) := by
  change homologyNorm L
    (motivicRawBaseEvaluationComparison L 1 1 (motivicCohomologyFieldChange φ 1 1 x)) = _
  rw [motivicCohomologyFieldChange_rawComparison]
  exact homologyNorm_fieldChange φ _

/-- The actual integral weight-one equivalence commutes with the original map on units. -/
theorem weightOneEquiv_fieldChange
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    weightOneEquiv L (motivicCohomologyFieldChange φ 1 1 x) =
      Additive.ofMul (Units.map φ.toMonoidHom (weightOneEquiv k x).toMul) :=
  motivicNorm_fieldChange φ x

/-- The original graph inverse commutes with the actual integral field map. -/
theorem weightOneEquiv_symm_fieldChange (a : kˣ) :
    motivicCohomologyFieldChange φ 1 1 ((weightOneEquiv k).symm (Additive.ofMul a)) =
      (weightOneEquiv L).symm (Additive.ofMul (Units.map φ.toMonoidHom a)) := by
  apply (weightOneEquiv L).injective
  rw [weightOneEquiv_fieldChange, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

/-- Reduction of each original integral unit graph is natural at every coefficient level. -/
theorem unitReduction_fieldChange (n : ℕ) (a : kˣ) :
    motivicFiniteCohomologyFieldChange φ 1 1 n (unitReduction k n (Additive.ofMul a)) =
      unitReduction L n (Additive.ofMul (Units.map φ.toMonoidHom a)) := by
  change motivicFiniteCohomologyFieldChange φ 1 1 n
    (motivicBaseIntegralReduction k 1 1 n ((weightOneEquiv k).symm (Additive.ofMul a))) = _
  rw [motivicCohomologyFieldChange_integralReduction, weightOneEquiv_symm_fieldChange]
  rfl

/-- The actual finite weight-one equivalence commutes with the induced unit-quotient map. -/
theorem weightOneFiniteEquiv_fieldChange (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :
    weightOneFiniteEquiv L n (motivicFiniteCohomologyFieldChange φ 1 1 n x) =
      (unitsModuloPowersFieldChange φ n).toAdditive (weightOneFiniteEquiv k n x) := by
  obtain ⟨a, ha⟩ := unitReduction_surjective k n x
  rw [← ha, ← ofMul_toMul a]
  rw [unitReduction_fieldChange, weightOneFiniteEquiv_unitReduction,
    weightOneFiniteEquiv_unitReduction]
  rfl

/-- On every literal unit coset, the inverse finite equivalence gives the ordinary image graph. -/
theorem weightOneFiniteEquiv_symm_mk_fieldChange (n : ℕ) (a : kˣ) :
    motivicFiniteCohomologyFieldChange φ 1 1 n
      ((weightOneFiniteEquiv k n).symm
        (Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n))) =
      (weightOneFiniteEquiv L n).symm
        (Additive.ofMul (QuotientGroup.mk (Units.map φ.toMonoidHom a) :
          unitsModuloPowers L n)) := by
  rw [weightOneFiniteEquiv_symm_mk, weightOneFiniteEquiv_symm_mk, unitReduction_fieldChange]

/-- In the computed integral weight-one group the actual identity-field map is the identity. -/
theorem integral_fieldChange_id
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    motivicCohomologyFieldChange (RingHom.id k) 1 1 x = x := by
  apply (weightOneEquiv k).injective
  rw [weightOneEquiv_fieldChange]
  rfl

/-- In finite weight one the actual identity-field map is the identity at every level. -/
theorem finite_fieldChange_id (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteCohomologyFieldChange (RingHom.id k) 1 1 n x = x := by
  obtain ⟨y, rfl⟩ := integralReduction_surjective k n x
  rw [motivicCohomologyFieldChange_integralReduction, integral_fieldChange_id]

variable {M : Type u} [Field M] (ψ : L →+* M)
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of M))) AddCommGrpCat.{u + 1})]

/-- The actual maps compose in computed integral weight one, by the ordinary units formula. -/
theorem integral_fieldChange_comp
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    motivicCohomologyFieldChange ψ 1 1 (motivicCohomologyFieldChange φ 1 1 x) =
      motivicCohomologyFieldChange (ψ.comp φ) 1 1 x := by
  apply (weightOneEquiv M).injective
  rw [weightOneEquiv_fieldChange, weightOneEquiv_fieldChange, weightOneEquiv_fieldChange]
  rfl

/-- The actual maps compose in computed finite weight one, at every coefficient level. -/
theorem finite_fieldChange_comp (n : ℕ)
    (x : motivicFiniteCohomology k 1 1 n (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteCohomologyFieldChange ψ 1 1 n (motivicFiniteCohomologyFieldChange φ 1 1 n x) =
      motivicFiniteCohomologyFieldChange (ψ.comp φ) 1 1 n x := by
  obtain ⟨y, rfl⟩ := integralReduction_surjective k n x
  rw [motivicCohomologyFieldChange_integralReduction,
    motivicCohomologyFieldChange_integralReduction,
    motivicCohomologyFieldChange_integralReduction, integral_fieldChange_comp]

end Motivic.WeightOneCohomologyFieldChange
