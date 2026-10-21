/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.QuasiAffine.FiniteNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # An affine étale refinement retaining the original full finite boundary -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Restricting the neighborhood along a monomorphism through which its full boundary
already factors retains the original cartesian boundary square. -/
theorem isPullback_boundary_refinement {Z Y Y' X : Scheme.{u}}
    (p : Y ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
    (hs : IsPullback s (𝟙 Z) p z) (r : Y' ⟶ Y) [Mono r]
    (t : Z ⟶ Y') (ht : t ≫ r = s) : IsPullback t (𝟙 Z) (r ≫ p) z := by
  have hw : t ≫ (r ≫ p) = 𝟙 Z ≫ z := by rw [← Category.assoc, ht, hs.w]
  apply IsPullback.of_isLimit' ⟨hw⟩
  refine PullbackCone.IsLimit.mk _ (fun c => c.snd) ?_ (by simp) ?_
  · intro c
    apply (cancel_mono r).mp
    rw [Category.assoc, ht]
    have hc : (c.fst ≫ r) ≫ p = c.snd ≫ z := by simpa [Category.assoc] using c.condition
    have hfirst := hs.lift_fst (c.fst ≫ r) c.snd hc
    have hsecond := hs.lift_snd (c.fst ≫ r) c.snd hc
    simp only [Category.comp_id] at hsecond
    simpa only [hsecond] using hfirst
  · intro c m _ hm
    simpa using hm

/-- The full boundary is retained as a scheme, including all nilpotents, inside an
actual affine open of the original quasi-affine neighborhood. -/
theorem exists_affine_boundary_refinement {Z Y X : Scheme.{u}} [Y.IsQuasiAffine]
    (p : Y ⟶ X) (z : Z ⟶ X) (s : Z ⟶ Y)
    (hs : IsPullback s (𝟙 Z) p z) (hZ : (Set.univ : Set Z).Finite) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (t : Z ⟶ U),
      t ≫ U.ι = s ∧ IsPullback t (𝟙 Z) (U.ι ≫ p) z := by
  obtain ⟨U, hU, hSU⟩ := exists_isAffineOpen_of_finite (Set.range s)
    (by simpa using hZ.image s)
  have hrange : Set.range s ⊆ Set.range U.ι := by simpa using hSU
  let t := IsOpenImmersion.lift U.ι s hrange
  have ht : t ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  exact ⟨U, hU, t, ht, isPullback_boundary_refinement p z s hs U.ι t ht⟩

/-- A separated quasi-compact étale neighborhood of an affine scheme admits an affine
open refinement without changing its full boundary finite over an arbitrary field. -/
theorem exists_affine_etale_boundary_refinement {k : Type u} [Field k]
    {Z Y X : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
    (z : Z ⟶ X) (s : Z ⟶ Y) (hs : IsPullback s (𝟙 Z) p z)
    (q : Z ⟶ Spec (.of k)) [IsFinite q] :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (t : Z ⟶ U),
      t ≫ U.ι = s ∧ IsPullback t (𝟙 Z) (U.ι ≫ p) z ∧ Etale (U.ι ≫ p) := by
  let : Y.IsQuasiAffine := isQuasiAffine_of_etale_affine_target p
  have hZ : (Set.univ : Set Z).Finite := by
    simpa using q.finite_preimage (Set.finite_univ : (Set.univ : Set (Spec (.of k))).Finite)
  obtain ⟨U, hU, t, ht, hs'⟩ := exists_affine_boundary_refinement p z s hs hZ
  exact ⟨U, hU, t, ht, hs', inferInstance⟩
end AlgebraicGeometry.Scheme
