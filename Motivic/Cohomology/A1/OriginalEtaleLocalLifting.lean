/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticOriginalEtalePresentation
public import Motivic.Cohomology.A1.OriginalEtalePresentationLifting

/-! # Original affine étale local lifting over an infinite field -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.RelativeCurve
open QuadraticIncidence.InfinityChart
universe u
namespace Motivic

/-- Construct the simultaneous presentation and the actual restriction-difference lifting
from the original affine étale square, without any presentation or finiteness premise. -/
theorem exists_original_etale_local_lifting
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
  obtain ⟨e⟩ := nonempty_originalEtalePresentation k B P J hJ g hg d hd p a s hs H ha hcover
  exact ⟨e, e.exists_lifting k _ p a _ s P F hF⟩

end Motivic
