/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.EtaleLineZeroFiber
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness and actual points of the original affine-line zero fiber -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The zero fiber of an etale line chart is smooth over the original field. -/
theorem etaleLineZeroFiber_smooth (k B : Type u) [Field k] [CommRing B]
    [Algebra k B] [Algebra.Smooth k B] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of (Polynomial B))) [Etale h] :
    Smooth (pullback.fst
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B)))) h ≫
        Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      ((RingHom.smooth_algebraMap (R := k) (S := B)).mpr inferInstance)
  infer_instance

/-- A point at which the original line coordinate vanishes belongs to the
actual closed zero fiber, without replacing its residue field. -/
theorem mem_range_etaleLineZeroFiber (B : Type u) [CommRing B] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of (Polynomial B))) (y : Y)
    (hy : Polynomial.X ∈ (h y).asIdeal) :
    y ∈ Set.range (pullback.snd
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B)))) h) := by
  rw [Scheme.Pullback.range_snd]
  change h y ∈ Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : B)))
  rw [range_comap_of_surjective _ _ (fun b => ⟨Polynomial.C b, by simp⟩)]
  rw [PrimeSpectrum.mem_zeroLocus, Polynomial.ker_evalRingHom]
  simp only [Polynomial.C_0, sub_zero]
  intro f hf
  exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy) :
    Ideal.span {Polynomial.X} ≤ (h y).asIdeal) hf

end AlgebraicGeometry.Scheme.Hom
