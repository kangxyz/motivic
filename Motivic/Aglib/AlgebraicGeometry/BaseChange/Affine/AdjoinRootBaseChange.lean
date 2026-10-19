/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdjoinRoot

/-! # Literal polynomial quotient base change over arbitrary coefficient maps -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.AdjoinRootBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (p : R[X])

/-- The actual quotient square commutes. -/
theorem square :
    CommRingCat.ofHom φ ≫ CommRingCat.ofHom (AdjoinRoot.of (p.map φ)) =
      CommRingCat.ofHom (AdjoinRoot.of p) ≫
        CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl) := by
  ext r
  simp

/-- The whole mapped quotient is the pushout, including noninjective scalar maps. -/
theorem isPushout :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (AdjoinRoot.of p))
      (CommRingCat.ofHom (AdjoinRoot.of (p.map φ)))
      (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl)) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (square φ p))
  apply PushoutCocone.isColimitAux'
  intro s
  have hc : s.inl.hom.comp φ = s.inr.hom.comp (AdjoinRoot.of p) :=
    congrArg CommRingCat.Hom.hom s.condition
  have hr : (p.map φ).eval₂ s.inl.hom (s.inr (AdjoinRoot.root p)) = 0 := by
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  let d : CommRingCat.of (AdjoinRoot (p.map φ)) ⟶ s.pt :=
    CommRingCat.ofHom (AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr)
  refine ⟨d, ?_, ?_, ?_⟩
  · ext r
    change AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
      (AdjoinRoot.of (p.map φ) r) = s.inl r
    simp
  · apply CommRingCat.hom_ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
        (AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.of p r)) = s.inr (AdjoinRoot.of p r)
      simpa using RingHom.congr_fun hc r
    · change AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr
        (AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.root p)) = s.inr (AdjoinRoot.root p)
      simp
  · intro m hm hn
    apply CommRingCat.hom_ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      have h := congrArg (fun f => f r) hm
      change m (AdjoinRoot.of (p.map φ) r) = s.inl r at h
      change m (AdjoinRoot.of (p.map φ) r) =
        AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr (AdjoinRoot.of (p.map φ) r)
      simpa using h
    · have hroot := congrArg (fun f => f (AdjoinRoot.root p)) hn
      change m (AdjoinRoot.map φ p (p.map φ) dvd_rfl (AdjoinRoot.root p)) =
        s.inr (AdjoinRoot.root p) at hroot
      change m (AdjoinRoot.root (p.map φ)) =
        AdjoinRoot.lift s.inl.hom (s.inr (AdjoinRoot.root p)) hr (AdjoinRoot.root (p.map φ))
      simpa using hroot

/-- Taking spectra identifies the whole mapped quotient with its scheme-theoretic fiber. -/
theorem isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (AdjoinRoot.of (p.map φ))))
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.map φ p (p.map φ) dvd_rfl)))
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout φ p)

end AlgebraicGeometry.AdjoinRootBaseChange
