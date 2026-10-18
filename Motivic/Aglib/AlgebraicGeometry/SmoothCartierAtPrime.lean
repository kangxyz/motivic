/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothPrimeParameterLine
public import Motivic.Aglib.AlgebraicGeometry.EtaleLineZeroFiberGeometry

/-! # Smooth Cartier divisors through actual positive-local-rank points

The original parameter in a smooth affine algebra is retained as the line
coordinate. Its literal zero fiber is flat-pulled back from the zero section,
so its original kernel ideal is locally rank one. An actual affine open chart
then transports this divisor to a neighborhood in an arbitrary smooth scheme.
No smooth divisor or perfection of the point's residue field is supplied.
-/
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
    rw [← ha]
    dsimp only [i]
    rw [← pullback.condition_assoc]
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

/-- Every positive-local-rank point of a smooth scheme over a perfect field lies
on an actual smooth Cartier divisor in an affine open neighborhood. Smoothness
and the point image use the original base morphism and original open immersion. -/
theorem exists_smooth_cartier_neighborhood
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (x : X)
    (hpos : 0 < ringKrullDim (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ U.toScheme),
        IsClosedImmersion i ∧ IsLocallyRankOne U.toScheme (Hom.idealModule i) ∧
        Smooth (i ≫ U.ι ≫ p) ∧ x ∈ Set.range (i ≫ U.ι) := by
  obtain ⟨R, a, ha, q, hq⟩ := X.exists_Spec_apply_eq x
  let : IsOpenImmersion a := ha
  let φ : k →+* R := (Spec.preimage (a ≫ p)).hom
  let : Algebra k R := φ.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k R)) = a ≫ p :=
    Spec.map_preimage _
  have : Algebra.Smooth k R := by
    apply (RingHom.smooth_algebraMap (R := k) (S := R)).mp
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
    rw [Spec.map_preimage]
    infer_instance
  have hqpos : 0 < ringKrullDim (Localization.AtPrime q.asIdeal) := by
    let e := asIso (a.stalkMap q) ≪≫ Spec.stalkIso R q
    rw [← ringKrullDim_eq_of_ringEquiv e.commRingCatIsoToRingEquiv]
    change 0 < ringKrullDim (X.presheaf.stalk (a q))
    rw [hq]
    exact hpos
  obtain ⟨r, _, Z, i, hi, hI, hs, y, hy, hz⟩ :=
    exists_smooth_cartier_at_prime k R q.asIdeal hqpos
  let : IsClosedImmersion i := hi
  let u : Spec (.of (Localization.Away r)) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ a
  let U := u.opensRange
  let e : Spec (.of (Localization.Away r)) ≅ U.toScheme :=
    IsOpenImmersion.isoOfRangeEq u U.ι (by simp [U])
  have he : e.hom ≫ U.ι = u := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  let j : Z ⟶ U.toScheme := i ≫ e.hom
  have hu : u ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
    dsimp only [u]
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    rfl
  have hyu : u y = x := by
    change a ((Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) y) = x
    rw [hy]
    exact hq
  have hj : j ≫ U.ι = i ≫ u := by
    dsimp only [j]
    rw [Category.assoc, he]
  have hI' : IsLocallyRankOne U.toScheme (Hom.idealModule j) := by
    have hw : 𝟙 Z ≫ i = j ≫ e.inv := by simp [j]
    let v := Hom.idealPullbackMap i j e.inv (𝟙 Z) hw
    have : IsIso v := Hom.idealPullbackMap_isIso_of_iso_square i j e.inv (𝟙 Z) hw
    exact isLocallyRankOne_of_iso _ (asIso v) (pullback_locallyRankOne e.inv _ hI)
  refine ⟨U, isAffineOpen_opensRange u, ⟨y, hyu⟩, Z, j, inferInstance, hI', ?_, ?_⟩
  · rw [← Category.assoc, hj, Category.assoc, hu]
    exact hs
  · obtain ⟨z, hz⟩ := hz
    refine ⟨z, ?_⟩
    rw [hj]
    change u (i z) = x
    rw [hz]
    exact hyu

end AlgebraicGeometry.Scheme
