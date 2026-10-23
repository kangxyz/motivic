/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Sections.FiniteFlatPair
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpenPair
/-! # The original fixed punctured-source sections in native twist coefficients -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (r : R)
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]

/-- The nonnegative twisting line bundle pulled back to the fixed ambient scheme. -/
def fixedPsiTwistLine (d : ℕ) : LineBundle (fixedPsiAmbient R r) :=
  pullbackLineBundle (fixedPsiProjectiveIso R r).hom
    (ProjectiveSpace.twistingLineBundle Γ((fixedPsiSource R r).toScheme, ⊤)
      (ULift.{u} (Fin 2)) (d : ℤ))

/-- Require finite flat zero schemes before and after restriction to the retained curve, containment
in that curve, and a monomorphic restricted functional. -/
def FixedPsiLineSectionFiniteFlat (L : LineBundle (fixedPsiAmbient R r))
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ L.val) : Prop :=
  let q := pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)
  let j := fixedPsiRetainedInclusion R r V
  let a := sectionDualFunctional (fixedPsiAmbient R r) L t
  IsFinite (Scheme.Modules.Hom.zeroInclusion a ≫ q) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion a ≫ q) ∧
    Set.range (Scheme.Modules.Hom.zeroInclusion a) ⊆ Set.range j ∧
    IsFinite (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit a j) ≫ j ≫ q) ∧
    Mono (Scheme.Modules.Hom.pullbackToUnit a j) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit a j) ≫ j ≫ q)

/-- Same original shrink, literal whole-boundary ratio, and both whole finite-flat divisors. -/
theorem exists_fixedPsiNormalizedSectionPair [IsNoetherianRing R]
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (e : (n : ℕ) → (Scheme.Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
      (ProjectiveSpace.twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      ∃ n t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
        (fixedPsiTwistLine R r d).val,
        pullbackSectionMap (fixedPsiBoundaryMap R r V) n =
          (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap (fixedPsiBoundaryMap R r V) t ∧
        IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) n) ∧
        IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) t) ∧
        FixedPsiLineSectionFiniteFlat R r V (fixedPsiTwistLine R r d) n ∧
        FixedPsiLineSectionFiniteFlat R r V (fixedPsiTwistLine R r d) t := by
  obtain ⟨N, hN⟩ := exists_fixedPsiFiniteFlatSectionPair R V hV r e
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨v, hv, n, t, hn, ht, hIn, hIt, _, _⟩ := hN d hd
  let T := fixedPsiTwistLine R r d
  let zD := fixedPsiBoundaryMap R r V
  let n0 := rightNormalizeSection T.val n
  let t0 := rightNormalizeSection T.val t
  have : IsIso (pullbackSectionMap zD n) := hIn
  have : IsIso (pullbackSectionMap zD t) := hIt
  have hn0 : IsIso (pullbackSectionMap zD n0) := by
    change IsIso ((pullbackUnitIso _).inv ≫ (Scheme.Modules.pullback _).map
      (n ≫ (tensorSheafRightUnit _ T.val).hom))
    rw [Functor.map_comp, ← Category.assoc]
    infer_instance
  have ht0 : IsIso (pullbackSectionMap zD t0) := by
    change IsIso ((pullbackUnitIso _).inv ≫ (Scheme.Modules.pullback _).map
      (t ≫ (tensorSheafRightUnit _ T.val).hom))
    rw [Functor.map_comp, ← Category.assoc]
    infer_instance
  refine ⟨n0, t0, ?_, hn0, ht0, ?_, ?_⟩
  · change pullbackSectionMap zD (rightNormalizeSection T.val n) =
      (fixedPsiBoundaryUnit R V r).hom ≫ pullbackSectionMap zD (rightNormalizeSection T.val t)
    rw [pullbackSectionMap_rightNormalize, pullbackSectionMap_rightNormalize]
    have hn' : pullbackSectionMap zD n ≫ pullbackTensorMap zD T.val _ =
        v ≫ tensorSheafMap _ (𝟙 _) ((pullbackUnitIso zD).hom ≫
          (fixedPsiBoundaryUnit R V r).hom ≫ (pullbackUnitIso zD).inv) := hn
    have ht' : pullbackSectionMap zD t ≫ pullbackTensorMap zD T.val _ = v := ht
    rw [← Category.assoc, hn', Category.assoc,
      ← Category.assoc (pullbackSectionMap zD t), ht']
    exact rightUnit_normalize_conjugate v (pullbackUnitIso zD) _
  · exact fixedPsiSectionDivisor_finite_mono_flat R r V T n0
  · exact fixedPsiSectionDivisor_finite_mono_flat R r V T t0
end AlgebraicGeometry.RelativeProjectiveLine
