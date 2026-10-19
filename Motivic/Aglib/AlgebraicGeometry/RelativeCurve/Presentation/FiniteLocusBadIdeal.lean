/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.FiniteChart.EnvelopeGoodOpen
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BoundaryPrescribedScheme
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality

/-! # A fixed original nonzero ideal controls the étale bad locus and prescribed scheme -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry

/-- A nonempty affine open has a nonzero ideal defining its complete closed complement. -/
theorem vanishingIdeal_complement_ne_bot (B : Type u) [CommRing B]
    (U : (Spec (.of B)).Opens) (hU : (U : Set (Spec (.of B))).Nonempty) :
    PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of B)))ᶜ ≠ ⊥ := by
  intro he
  have hz := PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
    (U : Set (Spec (.of B)))ᶜ
  rw [he, PrimeSpectrum.zeroLocus_bot, U.isOpen.isClosed_compl.closure_eq] at hz
  obtain ⟨x, hx⟩ := hU
  have hxc : x ∈ (U : Set (Spec (.of B)))ᶜ := by
    rw [← hz]
    exact Set.mem_univ x
  exact hxc hx

/-- Before choosing any projection, the original étale map has a fixed nonzero
bad ideal. Its closed scheme contains the entire prescribed nonreduced quotient. -/
theorem exists_fixed_finite_locus_bad_ideal
    (k B : Type u) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (J : Ideal B) (hJ : J ≠ ⊥) :
    ∃ I : Ideal B, I ≠ ⊥ ∧ I ≤ J ∧
      ∃ U : (Spec (.of B)).Opens,
        (U : Set (Spec (.of B))) = (PrimeSpectrum.zeroLocus (I : Set B))ᶜ ∧
        IsFinite (p ∣_ U) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have (x : Spec (.of B)) : IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) :=
    (Scheme.smoothFieldNormality k (Spec (.of B)) _ hsm x).2
  let V := Scheme.EtaleCompactification.finiteLocusOpen (Spec (.of B)) p
  have hV : (V : Set (Spec (.of B))).Nonempty :=
    ⟨genericPoint _, Scheme.EtaleCompactification.genericPoint_mem_finiteLocusOpen _ p⟩
  let K := PrimeSpectrum.vanishingIdeal (V : Set (Spec (.of B)))ᶜ
  have hK : K ≠ ⊥ := vanishingIdeal_complement_ne_bot B V hV
  let I := J * K
  let U : (Spec (.of B)).Opens :=
    ⟨(PrimeSpectrum.zeroLocus (I : Set B))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩
  have hUV : U ≤ V := by
    intro x hx
    by_contra hn
    apply hx
    apply PrimeSpectrum.zeroLocus_anti_mono_ideal Ideal.mul_le_right
    exact PrimeSpectrum.subset_zeroLocus_vanishingIdeal _ hn
  have := Scheme.EtaleCompactification.finite_on_finiteLocusOpen (Spec (.of B)) p
  refine ⟨I, ?_, Ideal.mul_le_left, U, rfl,
    Scheme.RelativeCurve.finite_morphismRestrict_of_le p hUV⟩
  exact fun h => (Ideal.mul_eq_bot.mp h).elim hJ hK

end AlgebraicGeometry
