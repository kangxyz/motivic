/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.OriginalAffineLocalVanishing
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! # The zero-dimensional branch of original-section detection -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]

omit [Infinite k] in
/-- In transcendence degree zero the original smooth domain is a field, so the
complement of any nonzero ideal is already the entire original affine scheme. -/
theorem section_zero_of_trdeg_zero (hd : Algebra.trdeg k B = 0)
    (J : Ideal B) (hJ : J ≠ ⊥)
    {A : SmoothSite (Spec (.of k))} (a : A ⟶ originalAffineObject k B)
    [IsOpenImmersion a.left]
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{w} k)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) : v = 0 := by
  have : Algebra.IsAlgebraic k B := (trdeg_eq_zero_iff).mp hd
  let : Field B := (isField_of_isIntegral_of_isField' (R := k) (S := B)
    (Field.toIsField k)).toField
  have htop : J = ⊤ := (Ideal.eq_bot_or_top J).resolve_left hJ
  have : Subsingleton (B ⧸ J) := by rw [htop]; infer_instance
  have : IsEmpty (PrimeSpectrum (B ⧸ J)) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr inferInstance
  have ha : Function.Surjective a.left := by
    intro y
    rcases hcover y with h | ⟨z, _⟩
    · exact h
    · exact isEmptyElim (show PrimeSpectrum (B ⧸ J) from z)
  have : Surjective a.left := ⟨ha⟩
  have : IsIso a.left := (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨inferInstance, inferInstance⟩
  have : IsIso ((SmoothSite.forgetScheme _).map a) := ‹IsIso a.left›
  have : IsIso a := isIso_of_reflects_iso a (SmoothSite.forgetScheme _)
  have : IsIso (P.transfer ((Cor.graphFunctor k).map a)) := inferInstance
  exact ((AddCommGrpCat.mono_iff_injective (P.transfer ((Cor.graphFunctor k).map a))).mp
    inferInstance)
    (hv.trans (map_zero _).symm)

end Motivic.PresheafWithTransfers
