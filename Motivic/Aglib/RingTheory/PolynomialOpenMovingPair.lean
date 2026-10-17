/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.ZeroNeighborhoodPencil

/-! # Moving a diagonal into a smaller polynomial open

The two disjoint boundaries are retained in the original polynomial ring.
Only the larger open's boundary is inverted at the source coordinate.
No invertibility on the smaller open or correspondence splitting is assumed.
-/
@[expose] public noncomputable section
open Polynomial ZeroNeighborhoodInterpolation
universe u
namespace Polynomial.OpenMovingPair
variable {R : Type u} [CommRing R]

/-- The diagonal factor has an actual polynomial inverse modulo the old boundary. -/
theorem exists_diagonal_inverse (f : R[X]) (a : R) (ha : IsUnit (f.eval a)) :
    ∃ r : R[X], f ∣ (X - C a) * r - 1 := by
  obtain ⟨v, hv⟩ := ha
  refine ⟨-C (↑(v⁻¹) : R) * dividedDifference f a, -C (↑(v⁻¹) : R), ?_⟩
  have hd := dividedDifference_mul f a
  have hu : C (↑(v⁻¹) : R) * C (f.eval a) = (1 : R[X]) := by
    rw [← hv, ← C_mul]
    simp
  linear_combination -C (↑(v⁻¹) : R) * hd + hu

/-- Actual CRT interpolation: inverse diagonal on the old boundary, one on the new boundary. -/
theorem exists_boundary_residue (f g : R[X]) (hfg : IsCoprime f g)
    (a : R) (ha : IsUnit (f.eval a)) :
    ∃ r : R[X], f ∣ (X - C a) * r - 1 ∧ g ∣ r - 1 := by
  obtain ⟨r, b, hb⟩ := exists_diagonal_inverse f a ha
  obtain ⟨u, v, huv⟩ := hfg
  refine ⟨r * v * g + u * f, ?_, ?_⟩
  · refine ⟨b * v * g + ((X - C a) - 1) * u, ?_⟩
    linear_combination v * g * hb + huv
  · refine ⟨(r - 1) * v, ?_⟩
    linear_combination huv

/-- Produce both monic endpoints, with the precise degree difference needed for a pencil. -/
theorem exists_monic_pair [Nontrivial R] (f g : R[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : IsCoprime f g) (a : R) (ha : IsUnit (f.eval a)) :
    ∃ d q : R[X], d.Monic ∧ q.Monic ∧ q.natDegree = d.natDegree + 1 ∧
      f ∣ (X - C a) * d - 1 ∧ g ∣ d - 1 ∧ f * g ∣ q - 1 := by
  obtain ⟨r, hr, hrg⟩ := exists_boundary_residue f g hfg a ha
  let N := r.natDegree
  let d := monicLift (f * g) r N
  let q := monicLift (f * g) 1 (N + 1)
  have hd := monicLift_monic_natDegree (f * g) r (hf.mul hg) N le_rfl
  have hq := monicLift_monic_natDegree (f * g) 1 (hf.mul hg) (N + 1) (by simp)
  have hdf : f ∣ d - r := dvd_trans (dvd_mul_right f g) (monicLift_boundary _ _ _)
  have hdg : g ∣ d - r := dvd_trans (dvd_mul_left g f) (monicLift_boundary _ _ _)
  refine ⟨d, q, hd.1, hq.1, ?_, ?_, ?_, monicLift_boundary _ _ _⟩
  · rw [hq.2, hd.2]
    omega
  · convert dvd_add (dvd_mul_of_dvd_right hdf (X - C a)) hr using 1
    ring
  · convert dvd_add hdg hrg using 1
    ring

/-- A Bezout identity forces the entire boundary to be invertible on the whole zero scheme. -/
theorem boundary_unit (p f r : R[X]) (h : f ∣ r * p - 1) :
    IsUnit (AdjoinRoot.mk p f) := by
  obtain ⟨b, hb⟩ := h
  have hc : IsCoprime p f := ⟨r, -b, by linear_combination hb⟩
  simpa only [AdjoinRoot.mk_self, isCoprime_zero_left] using
    hc.map (AdjoinRoot.mk p)

/-- Both correction terms land in the smaller open; the whole homotopy stays in the old open. -/
theorem exists_finite_free_moving_pencil [Nontrivial R]
    (f g : R[X]) (hf : f.Monic) (hg : g.Monic) (hfg : IsCoprime f g)
    (a : R) (ha : IsUnit (f.eval a)) :
    ∃ d q : R[X], d.Monic ∧ q.Monic ∧
      q.natDegree = ((X - C a) * d).natDegree ∧
      IsUnit (AdjoinRoot.mk d (f * g)) ∧ IsUnit (AdjoinRoot.mk q (f * g)) ∧
      (pencil ((X - C a) * d) q).Monic ∧
      Module.Finite R[X] (AdjoinRoot (pencil ((X - C a) * d) q)) ∧
      Module.Free R[X] (AdjoinRoot (pencil ((X - C a) * d) q)) ∧
      IsUnit (AdjoinRoot.mk (pencil ((X - C a) * d) q) (f.map C)) := by
  obtain ⟨d, q, hd, hq, hdeg, hfd, hgd, hfgq⟩ := exists_monic_pair f g hf hg hfg a ha
  have hp : ((X - C a) * d).Monic := (monic_X_sub_C a).mul hd
  have heq : q.natDegree = ((X - C a) * d).natDegree := by
    rw [Monic.natDegree_mul (monic_X_sub_C a) hd, natDegree_X_sub_C, hdeg]
    omega
  have hduf := boundary_unit d f (X - C a) hfd
  have hdug := boundary_unit d g 1 (by simpa using hgd)
  have hqu := boundary_unit q (f * g) 1 (by simpa using hfgq)
  refine ⟨d, q, hd, hq, heq, ?_, hqu,
    (pencil_monic_natDegree hp hq heq).1,
    (pencil_finite_free hp hq heq).1, (pencil_finite_free hp hq heq).2, ?_⟩
  · rw [map_mul]
    exact hduf.mul hdug
  · exact pencil_boundary_unit f _ _ hfd (dvd_trans (dvd_mul_right f g) hfgq)

end Polynomial.OpenMovingPair
