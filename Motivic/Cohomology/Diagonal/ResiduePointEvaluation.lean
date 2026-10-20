/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.FiniteFundamentalEvaluation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamilies.FiniteAffineEndpointBranches

/-!
# Intrinsic residue-point evaluation of full finite fundamental cycles

Every actual residue field and every original local multiplicity is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u
namespace Motivic.DiagonalResiduePointEvaluation
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom
open DiagonalPointNorm DiagonalFinitePointEvaluation MilnorK

variable {k : Type u} [Field k] {T : Scheme.{u}} {q : ℕ}

/-- The literal evaluation of global sections at an actual residue point. -/
theorem fromSpecResidueField_appTop (x : T) :
    (T.fromSpecResidueField x).appTop ≫
      (Scheme.ΓSpecIso (T.residueField x)).hom = T.Γevaluation x := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  rw [Category.assoc, Scheme.ΓSpecIso_naturality]
  change T.presheaf.germ ⊤ x trivial ≫
    (Scheme.ΓSpecIso (T.presheaf.stalk x)).inv ≫
    (Spec (T.presheaf.stalk x)).presheaf.map (𝟙 _) ≫
    (Scheme.ΓSpecIso (T.presheaf.stalk x)).hom ≫ T.residue x = _
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  rfl

/-- The actual structural field map at a point, not an abstract field choice. -/
def residueScalar (p : T ⟶ Spec (.of k)) (x : T) : k →+* T.residueField x :=
  (T.Γevaluation x).hom.comp (WeightOneFundamentalNorm.schemeScalarMap p)

/-- The algebra structure induced by the actual structural scalar map at the residue point. -/
abbrev residueAlgebra (p : T ⟶ Spec (.of k)) (x : T) :
    Algebra k (T.residueField x) := (residueScalar p x).toAlgebra

/-- The residue-point structural map is the spectrum of its literal scalar map. -/
theorem residue_projection (p : T ⟶ Spec (.of k)) (x : T) :
    T.fromSpecResidueField x ≫ p =
      Spec.map (CommRingCat.ofHom (residueScalar p x)) := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (T.residueField x)).hom).mp
  rw [Scheme.Hom.comp_appTop, Category.assoc, fromSpecResidueField_appTop,
    Scheme.ΓSpecIso_naturality]
  change p.appTop ≫ T.Γevaluation x =
    (Scheme.ΓSpecIso (.of k)).hom ≫
      (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ T.Γevaluation x
  simp

/-- Every coordinate is evaluated in the actual residue field of the original point. -/
theorem residue_coordinate (j : T ⟶ ambient k q) (x : T) (i : Fin q) :
    affineCoordinateUnit (T.fromSpecResidueField x ≫ j) i =
      Units.map (T.Γevaluation x).hom.toMonoidHom
        (DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit j i) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (T.residueField x)).hom
    (((T.fromSpecResidueField x ≫ j) ≫ ambientCoordinate k q i).appTop
      (Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val) = _
  rw [Category.assoc, Scheme.Hom.comp_appTop]
  exact ConcreteCategory.congr_hom (fromSpecResidueField_appTop x)
    ((j ≫ ambientCoordinate k q i).appTop
      (Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val)

/-- Finiteness over the base field supplies discreteness and all point finiteness. -/
theorem finiteSchemeArtinian (p : T ⟶ Spec (.of k)) [IsFinite p] :
    IsArtinianScheme T :=
  { toIsLocallyArtinian := .of_locallyQuasiFinite p
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }

/-- The actual point set is finite, without an enumeration hypothesis. -/
abbrev finiteSchemeFintype (p : T ⟶ Spec (.of k)) [IsFinite p] : Fintype T := by
  let : IsArtinianScheme T := finiteSchemeArtinian p
  exact Fintype.ofFinite T

variable [DiscreteTopology T]

instance residueClosed (x : T) : IsClosedImmersion (T.fromSpecResidueField x) :=
  isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)

omit [DiscreteTopology T] in
theorem residueFinite (p : T ⟶ Spec (.of k)) [IsFinite p] (x : T) :
    let : Algebra k (T.residueField x) := residueAlgebra p x
    Module.Finite k (T.residueField x) := by
  let : Algebra k (T.residueField x) := residueAlgebra p x
  let : IsArtinianScheme T := finiteSchemeArtinian p
  have h : IsFinite (Spec.map (CommRingCat.ofHom (residueScalar p x))) := by
    rw [← residue_projection]
    infer_instance
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h)

/-- Pushing a residue point into the original scheme gives coefficient one. -/
theorem residue_fundamental (x : T) :
    IntegralCycle.finitePushforward (T.fromSpecResidueField x)
      (fundamentalCycle (Spec (T.residueField x))) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure x) 1 := by
  rw [fundamentalCycle_of_isIntegral, IntegralCycle.finitePushforward_single]
  have hs : (IntegralClosedSubscheme.pointClosure
      (genericPoint (Spec (T.residueField x)))).finiteImage (T.fromSpecResidueField x) =
      IntegralClosedSubscheme.pointClosure x := by
    apply IntegralClosedSubscheme.point_injective
    simp only [IntegralClosedSubscheme.point_finiteImage,
      IntegralClosedSubscheme.point_pointClosure, Scheme.fromSpecResidueField_apply]
  simp only [hs, residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]

variable [Finite T] [IsNoetherian T]

/-- The full fundamental cycle is the sum over all actual residue points.
Original nonreduced local multiplicities are unchanged. -/
theorem fundamental_eq_residue_sum :
    let : Fintype T := Fintype.ofFinite T
    fundamentalCycle T = ∑ x : T,
      (IntegralCycle.toPoints (fundamentalCycle T) x) •
        IntegralCycle.finitePushforward (T.fromSpecResidueField x)
          (fundamentalCycle (Spec (T.residueField x))) := by
  classical
  let : Fintype T := Fintype.ofFinite T
  apply IntegralCycle.toPoints_injective
  simp only [map_sum, residue_fundamental,
    IntegralCycle.toPoints_single, IntegralClosedSubscheme.point_pointClosure,
    Finsupp.smul_single, smul_eq_mul, mul_one]
  ext y
  simp

variable [CharZero k]

/-- A single actual residue point contributes its true Milnor norm. -/
def residueValue (p : T ⟶ Spec (.of k)) [IsFinite p]
    (a : Fin q → Γ(T, ⊤)ˣ) (x : T) : K k q := by
  let : Algebra k (T.residueField x) := residueAlgebra p x
  let : Module.Finite k (T.residueField x) := residueFinite p x
  exact finiteExtensionNorm k (T.residueField x) q
    (symbol (fun i => Units.map (T.Γevaluation x).hom.toMonoidHom (a i)))

/-- Evaluation of any full finite fundamental pushforward as actual residue norms,
with the literal original fundamental coefficients and coordinates. -/
theorem cycleValue_eq_residue_sum
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k q) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom = p)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    let : Fintype T := Fintype.ofFinite T
    cycleValue k q α = ∑ x : T,
      (IntegralCycle.toPoints (fundamentalCycle T) x) •
        residueValue p (DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit j) x := by
  classical
  let : Fintype T := Fintype.ofFinite T
  let (x : T) : Algebra k (T.residueField x) := residueAlgebra p x
  let (x : T) : Module.Finite k (T.residueField x) := residueFinite p x
  have hx (x : T) : (T.fromSpecResidueField x ≫ j) ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) q).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (T.residueField x))) := by
    rw [Category.assoc, hp]
    exact residue_projection p x
  let β : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q :=
    ∑ x : T, (IntegralCycle.toPoints (fundamentalCycle T) x) •
      finitePointCorrespondence (E := T.residueField x) (T.fromSpecResidueField x ≫ j) (hx x)
  have hβ : FiniteCorrespondence.toIntegralCycle β =
      IntegralCycle.finitePushforward j (fundamentalCycle T) := by
    rw [fundamental_eq_residue_sum]
    simp only [β, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro x _
    rw [toIntegralCycle_finitePointCorrespondence (E := T.residueField x),
      IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    rfl
  have he : α = β := FiniteCorrespondence.toIntegralCycle_injective (hα.trans hβ.symm)
  rw [he]
  simp only [β, map_sum, map_zsmul, cycleValue_finitePointCorrespondence]
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  exact congrArg symbol (funext (residue_coordinate j x))

omit [DiscreteTopology T] [Finite T] in
/-- The intrinsic full residue sum for an arbitrary finite scheme over the field.
The point finiteness and discreteness hypotheses are derived internally. -/
theorem cycleValue_eq_residue_sum_of_finite
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k q) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom = p)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    let : Fintype T := finiteSchemeFintype p
    cycleValue k q α = ∑ x : T,
      (IntegralCycle.toPoints (fundamentalCycle T) x) •
        residueValue p (DiagonalFiniteFundamentalEvaluation.schemeCoordinateUnit j) x := by
  let : IsArtinianScheme T := finiteSchemeArtinian p
  exact cycleValue_eq_residue_sum p j hp α hα

end Motivic.DiagonalResiduePointEvaluation
