/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Support
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.Cycle

/-!
# Signed finite correspondences under arbitrary field change

Every generator is sent to the sum of all reduced components of its actual
whole pulled-back support, weighted by the generic local lengths in that
whole support. The operation extends additively to all signed cycles. Its
faithful integral-cycle representation is exactly finite pushforward of the
whole fundamental cycle, including nilpotents, image collisions, and empty
supports. No compatibility with correspondence composition is asserted here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- Forgetting admissibility leaves the exact reduced component's finite image. -/
@[simp]
theorem toIntegralClosedSubscheme_fieldBaseChangeComponentGenerator
    (w : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentGenerator φ w).toIntegralClosedSubscheme =
      (IntegralClosedSubscheme.pointClosure w.1).finiteImage
        (A.fieldBaseChangeInclusion φ) := by
  apply Subtype.ext
  exact A.fieldBaseChangeComponentGenerator_val φ w

/-- Assemble all actual components with their supplied integer coefficients.
The closed immersion contributes residue degree one. -/
def fieldBaseChangeCycleAssembly :
    (genericPoints (A.fieldBaseChangeSupport φ) → ℤ) →+
      FiniteCorrespondence ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom := by
  classical
  letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  exact
    { toFun := fun c => ∑ w, Finsupp.single (A.fieldBaseChangeComponentGenerator φ w) (c w)
      map_zero' := by simp
      map_add' := by intro c d; simp [Finsupp.single_add, Finset.sum_add_distrib] }

/-- Every component is included, without selecting one after splitting. -/
theorem fieldBaseChangeCycleAssembly_eq_sum
    (c : genericPoints (A.fieldBaseChangeSupport φ) → ℤ) :
    A.fieldBaseChangeCycleAssembly φ c =
      letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
      ∑ w, Finsupp.single (A.fieldBaseChangeComponentGenerator φ w) (c w) := rfl

open Classical in
/-- Colliding finite images retain the sum of all original signed coefficients. -/
theorem fieldBaseChangeCycleAssembly_coefficient
    (c : genericPoints (A.fieldBaseChangeSupport φ) → ℤ)
    (B : FiniteCorrespondenceGenerator ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom) :
    A.fieldBaseChangeCycleAssembly φ c B =
      letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
      ∑ w, if A.fieldBaseChangeComponentGenerator φ w = B then c w else 0 := by
  rw [fieldBaseChangeCycleAssembly_eq_sum, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]

/-- The literal finite-image assembly agrees with actual integral-cycle pushforward. -/
theorem toIntegralCycle_fieldBaseChangeCycleAssembly
    (c : genericPoints (A.fieldBaseChangeSupport φ) → ℤ) :
    FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycleAssembly φ c) =
      IntegralCycle.finitePushforward (A.fieldBaseChangeInclusion φ)
        (IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeSupport φ) c) := by
  classical
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  rw [fieldBaseChangeCycleAssembly_eq_sum, IntegralCycle.ofGenericCoefficients_eq_sum,
    map_sum, map_sum]
  simp only [FiniteCorrespondence.toIntegralCycle_single,
    toIntegralClosedSubscheme_fieldBaseChangeComponentGenerator,
    IntegralCycle.finitePushforward_single, residueDegree_of_surjectiveOnStalks,
    Nat.cast_one, mul_one]

/-- The generator's actual field change, with lengths in the unreduced whole support. -/
def fieldBaseChangeCycle :
    FiniteCorrespondence ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom :=
  A.fieldBaseChangeCycleAssembly φ (fun w => (genericMultiplicity w : ℤ))

/-- The exact weighted finite sum defining field change on a generator. -/
theorem fieldBaseChangeCycle_eq_sum :
    A.fieldBaseChangeCycle φ =
      letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
      ∑ w, Finsupp.single (A.fieldBaseChangeComponentGenerator φ w)
        (genericMultiplicity w : ℤ) := rfl

/-- The original whole support supplies the fundamental multiplicities. -/
theorem toIntegralCycle_fieldBaseChangeCycle :
    FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycle φ) =
      IntegralCycle.finitePushforward (A.fieldBaseChangeInclusion φ)
        (fundamentalCycle (A.fieldBaseChangeSupport φ)) := by
  rw [fieldBaseChangeCycle, toIntegralCycle_fieldBaseChangeCycleAssembly,
    IntegralCycle.ofGenericCoefficients_genericMultiplicity]

/-- An empty whole support contributes the zero correspondence. -/
@[simp] theorem fieldBaseChangeCycle_of_isEmpty
    [IsEmpty (A.fieldBaseChangeSupport φ)] : A.fieldBaseChangeCycle φ = 0 := by
  classical
  rw [fieldBaseChangeCycle_eq_sum]
  simp

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y : SmoothSite.overField k}

/-- Actual field change on the free abelian group of finite correspondences. -/
def fieldBaseChange : FiniteCorrespondence X.hom Y.hom →+
    FiniteCorrespondence ((SmoothSite.fieldBaseChange φ).obj X).hom
      ((SmoothSite.fieldBaseChange φ).obj Y).hom :=
  Finsupp.liftAddHom fun A =>
    { toFun := fun n => n • A.fieldBaseChangeCycle φ
      map_zero' := by simp
      map_add' := by intro m n; exact add_zsmul _ _ _ }

theorem fieldBaseChange_single
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℤ) :
    fieldBaseChange (X := X) (Y := Y) φ (Finsupp.single A n) = n • A.fieldBaseChangeCycle φ :=
  Finsupp.liftAddHom_apply_single _ _ _

@[simp] theorem fieldBaseChange_single_simp
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℤ) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := Y) φ) (Finsupp.single A n) =
      n • A.fieldBaseChangeCycle φ :=
  fieldBaseChange_single φ A n

theorem fieldBaseChange_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
    fieldBaseChange (X := X) (Y := Y) φ A.cycle = A.fieldBaseChangeCycle φ := by
  simp only [FiniteCorrespondenceGenerator.cycle, fieldBaseChange_single, one_zsmul]

@[simp] theorem fieldBaseChange_cycle_simp
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := Y) φ) A.cycle =
      A.fieldBaseChangeCycle φ :=
  fieldBaseChange_cycle φ A

/-- All original signed coefficients multiply the whole-support fundamental cycles. -/
theorem toIntegralCycle_fieldBaseChange_single
    (A : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℤ) :
    toIntegralCycle (fieldBaseChange (X := X) (Y := Y) φ (Finsupp.single A n)) =
      n • IntegralCycle.finitePushforward (A.fieldBaseChangeInclusion φ)
        (fundamentalCycle (A.fieldBaseChangeSupport φ)) := by
  rw [fieldBaseChange_single, map_zsmul,
    FiniteCorrespondenceGenerator.toIntegralCycle_fieldBaseChangeCycle]

/-- Signed field change is the finite sum of the actual pulled-support pushforwards. -/
theorem toIntegralCycle_fieldBaseChange (α : FiniteCorrespondence X.hom Y.hom) :
    toIntegralCycle (fieldBaseChange (X := X) (Y := Y) φ α) =
      α.sum (fun A n => n • IntegralCycle.finitePushforward (A.fieldBaseChangeInclusion φ)
        (fundamentalCycle (A.fieldBaseChangeSupport φ))) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single α]
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro A _
  exact toIntegralCycle_fieldBaseChange_single φ A (α A)

theorem fieldBaseChange_add (α β : FiniteCorrespondence X.hom Y.hom) :
    fieldBaseChange (X := X) (Y := Y) φ (α + β) =
      fieldBaseChange (X := X) (Y := Y) φ α +
        fieldBaseChange (X := X) (Y := Y) φ β := map_add _ _ _

@[simp] theorem fieldBaseChange_add_simp (α β : FiniteCorrespondence X.hom Y.hom) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := Y) φ) (α + β) =
      fieldBaseChange (X := X) (Y := Y) φ α +
        fieldBaseChange (X := X) (Y := Y) φ β :=
  fieldBaseChange_add φ α β

theorem fieldBaseChange_neg (α : FiniteCorrespondence X.hom Y.hom) :
    fieldBaseChange (X := X) (Y := Y) φ (-α) = -fieldBaseChange (X := X) (Y := Y) φ α := map_neg _ _

@[simp] theorem fieldBaseChange_neg_simp (α : FiniteCorrespondence X.hom Y.hom) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := Y) φ) (-α) =
      -fieldBaseChange (X := X) (Y := Y) φ α :=
  fieldBaseChange_neg φ α

theorem fieldBaseChange_zsmul (n : ℤ) (α : FiniteCorrespondence X.hom Y.hom) :
    fieldBaseChange (X := X) (Y := Y) φ (n • α) =
      n • fieldBaseChange (X := X) (Y := Y) φ α := map_zsmul _ _ _

@[simp] theorem fieldBaseChange_zsmul_simp (n : ℤ) (α : FiniteCorrespondence X.hom Y.hom) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.snd X.hom (Spec.map (CommRingCat.ofHom φ)))
          (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))))
      _ _ _ (fieldBaseChange (X := X) (Y := Y) φ) (n • α) =
      n • fieldBaseChange (X := X) (Y := Y) φ α :=
  fieldBaseChange_zsmul φ n α

end FiniteCorrespondence

end Motivic
