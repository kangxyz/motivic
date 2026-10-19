/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.AffineDivisorEtaleComparison
public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Affine presentations of the original smooth Cartier pair -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- Smoothness of the original surjective target descends to its literal
principal quotient, with the original base algebra structure. -/
theorem formallySmooth_principal_quotient_of_surjective
    {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] (q : R →+* S) (hq : Function.Surjective q)
    (t : R) (hker : RingHom.ker q = Ideal.span {t})
    (hs : (q.comp (algebraMap k R)).Smooth) :
    Algebra.FormallySmooth k (R ⧸ Ideal.span {t}) := by
  let : Algebra k S := (q.comp (algebraMap k R)).toAlgebra
  let f : R →ₐ[k] S := ⟨q, fun x ↦ rfl⟩
  have : Algebra.Smooth k S := hs
  have e := Ideal.quotientKerAlgEquivOfSurjective (f := f) hq
  have : Algebra.FormallySmooth k (R ⧸ RingHom.ker q) :=
    Algebra.FormallySmooth.of_equiv e.symm
  rw [← hker]
  exact this

/-- The actual affine kernel of a smooth Cartier pair has a regular generator;
both section algebras are smooth over the original field. -/
theorem exists_smooth_affine_cartier_presentation
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (p : X ⟶ Spec (.of k))
    [Smooth p] [Smooth (i ≫ p)]
    (hI : IsLocallyRankOne X (Scheme.Hom.idealModule i)) (z : Z) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), ∃ hz : i z ∈ U,
      ∃ (t : Γ(X, U)) (φ : k →+* Γ(X, U)),
        φ = ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U (by simp)).hom ∧
        IsRegular t ∧ RingHom.ker (i.app U).hom = Ideal.span {t} ∧
        φ.Smooth ∧ ((i.app U).hom.comp φ).Smooth ∧
        t ∈ (hU.primeIdealOf ⟨i z, hz⟩).asIdeal := by
  obtain ⟨U, hU, hz, t, ht, hker⟩ :=
    i.exists_affine_regular_idealGenerator_of_isLocallyRankOne hI (i z)
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U (by simp)).hom
  have hφ : φ.Smooth := by
    dsimp only [φ]
    rw [CommRingCat.hom_comp, RingHom.Smooth.respectsIso.cancel_left_isIso]
    exact p.smooth_appLE (isAffineOpen_top _) hU _
  have hZ : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  have hφZ : ((i.app U).hom.comp φ).Smooth := by
    change (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U (by simp)) ≫ i.app U).hom.Smooth
    rw [Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [CommRingCat.hom_comp, RingHom.Smooth.respectsIso.cancel_left_isIso]
    exact (i ≫ p).smooth_appLE (isAffineOpen_top _) hZ _
  have htzero : (i.app U).hom t = 0 := by
    apply RingHom.mem_ker.mp
    rw [hker]
    exact Ideal.subset_span (by simp)
  have htp : t ∈ (hU.primeIdealOf ⟨i z, hz⟩).asIdeal := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU (i ⁻¹ᵁ U) hZ le_rfl hz]
    change (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom t ∈ (hZ.primeIdealOf ⟨z, hz⟩).asIdeal
    simpa only [Scheme.Hom.appLE_eq_app, htzero] using
      (hZ.primeIdealOf ⟨z, hz⟩).asIdeal.zero_mem
  exact ⟨U, hU, hz, t, φ, rfl,
    (Commute.isRegular_iff (fun b ↦ Commute.all t b)).mpr ht, hker, hφ, hφZ, htp⟩

end AlgebraicGeometry.Scheme
