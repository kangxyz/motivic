/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Density of the actual Cartier complement -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u

namespace PrimeSpectrum

/-- Inverting a regular element gives a dense principal open, without a
Noetherian or reducedness assumption. -/
theorem dense_basicOpen_of_isRegular {R : Type u} [CommRing R]
    (a : R) (ha : IsRegular a) : Dense (basicOpen a : Set (PrimeSpectrum R)) := by
  have hinj : Function.Injective (algebraMap R (Localization.Away a)) := by
    apply IsLocalization.injectiveₛ (M := Submonoid.powers a)
    rintro _ ⟨n, rfl⟩
    exact IsRegular.pow n ha
  have hd : DenseRange (comap (algebraMap R (Localization.Away a))) := by
    apply (denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  change Dense (Set.range (comap (algebraMap R (Localization.Away a)))) at hd
  rwa [localization_away_comap_range (Localization.Away a) a] at hd

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed immersion with locally rank-one actual ideal has dense complement.
The proof uses regular generators of the original affine ring kernels; no
smoothness, perfectness, integrality or chosen global equation is required. -/
theorem dense_compl_range_of_isLocallyRankOne {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) : Dense (Set.range i)ᶜ := by
  apply dense_iff_inter_open.mpr
  rintro N hN ⟨x, hx⟩
  obtain ⟨U, hU, hxU, a, ha, hker⟩ :=
    i.exists_affine_regular_idealGenerator_of_isLocallyRankOne hI x
  have hreg : IsRegular a :=
    (Commute.isRegular_iff (fun b ↦ Commute.all a b)).mpr ha
  have hopen : IsOpen (hU.fromSpec ⁻¹' N) := hN.preimage hU.fromSpec.continuous
  have hnonempty : (hU.fromSpec ⁻¹' N).Nonempty := by
    refine ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_⟩
    change hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ N
    simpa only [hU.fromSpec_primeIdealOf] using hx
  obtain ⟨q, hqN, hqa⟩ :=
    (PrimeSpectrum.dense_basicOpen_of_isRegular a hreg).inter_open_nonempty
      (hU.fromSpec ⁻¹' N) hopen hnonempty
  refine ⟨hU.fromSpec q, hqN, ?_⟩
  rintro ⟨z, hz⟩
  have hzU : i z ∈ U := by
    rw [hz]
    change hU.fromSpec q ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self q
  have hV : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have ha0 : (i.app U).hom a = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (by simp)
  have hap : a ∈ (hU.primeIdealOf ⟨i z, hzU⟩).asIdeal := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU (i ⁻¹ᵁ U) hV le_rfl hzU]
    change (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom a ∈
      (hV.primeIdealOf ⟨z, hzU⟩).asIdeal
    simpa only [Scheme.Hom.appLE_eq_app, ha0] using
      (hV.primeIdealOf ⟨z, hzU⟩).asIdeal.zero_mem
  have hq : hU.primeIdealOf ⟨i z, hzU⟩ = q := by
    apply hU.fromSpec.isOpenEmbedding.injective
    exact (hU.fromSpec_primeIdealOf ⟨i z, hzU⟩).trans hz
  rw [hq] at hap
  exact hqa hap

end AlgebraicGeometry.Scheme.Hom
