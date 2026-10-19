/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Original.EtaleLocalLifting
public import Lean

/-! # Original affine étale local lifting over an infinite field -/
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.RelativeCurve
open QuadraticIncidence.InfinityChart
universe u
namespace Motivic

example
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} [IsAffine Y] [IsAffine A] (p : Y ⟶ Spec (.of B))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (F : PresheafWithTransfers.{u + 1} k) (hF : F.IsA1Invariant) :
    ∃ e : OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s P,
      e.HasLocalLifting k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
        p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s P F := by
  exact exists_original_etale_local_lifting k B P J hJ g hg d hd p a s hs H ha hcover F hF

open Lean in
run_cmd do
  for name in #[``exists_original_etale_local_lifting,
      ``nonempty_originalEtalePresentation,
      ``OriginalEtalePresentation.exists_lifting] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original affine etale local lifting: complete producer-consumer, standard axioms."

end Motivic
