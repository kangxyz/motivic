/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothPrimeParameterLine
public import Motivic.Aglib.AlgebraicGeometry.EtaleLineZeroFiberGeometry

/-! # Construction of a smooth Cartier divisor through an actual positive-rank prime -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- On an actual principal neighborhood of the original prime, the literal
zero fiber supplies a smooth Cartier divisor containing its original lift. -/
theorem exists_smooth_cartier_at_prime
    (k R : Type u) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ r ∉ p, ∃ (Z : Scheme.{u}) (i : Z ⟶ Spec (.of (Localization.Away r))),
      IsClosedImmersion i ∧ IsLocallyRankOne _ (Hom.idealModule i) ∧
      Smooth (i ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) ∧
      ∃ q : Spec (.of (Localization.Away r)),
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) q =
          (⟨p, inferInstance⟩ : PrimeSpectrum R) ∧ q ∈ Set.range i := by
  classical
  obtain ⟨f, hf, d, c, r, hr, ψ, hψ, hX⟩ :=
    Algebra.exists_prime_parameter_etale_line_chart k R p hpos
  let B := MvPolynomial {j : Fin d // j ≠ c} k
  let Y := Spec (.of (Localization.Away r))
  let h : Y ⟶ Spec (.of (Polynomial B)) := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have : Etale h := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hψ
  let z := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : B)))
  have : IsClosedImmersion z := IsClosedImmersion.spec_of_surjective _
    (fun b => ⟨Polynomial.C b, by simp⟩)
  let i := pullback.snd z h
  have hw : i ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) =
      pullback.fst z h ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    have ha : h ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial B))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext ψ.comp_algebraMap
    rw [← ha, ← Category.assoc, ← pullback.condition_assoc]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext a
    simp
  have hsm : Smooth (i ≫ Spec.map
      (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) := by
    rw [hw]
    exact Hom.etaleLineZeroFiber_smooth k B h
  have hq : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨q, hq⟩ := hq
  refine ⟨r, hr, pullback z h, i, inferInstance,
    Hom.etaleLineZeroFiber_isLocallyRankOne B h, hsm, q, hq, ?_⟩
  apply Hom.mem_range_etaleLineZeroFiber B h q
  change ψ Polynomial.X ∈ q.asIdeal
  rw [hX]
  have he := congrArg (fun t : PrimeSpectrum R => f ∈ t.asIdeal) hq
  exact he.mpr hf

end AlgebraicGeometry.Scheme
