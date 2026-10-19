/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.QuadraticOriginalEtalePresentation
public import Motivic.Aglib.AlgebraicGeometry.PolynomialQuotientCoordinates
public import Motivic.Aglib.AlgebraicGeometry.PolynomialQuotientComplement
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Original étale presentation for the whole polynomial zero section

Finite generators and the positive dimension are derived from the smooth
integral coefficient algebra. The original zero square is transported through
its canonical linear-quotient isomorphism, without reducing the closed scheme
or assuming a rational selected point.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.RelativeCurve AlgebraicGeometry.PolynomialOpenQuotient

universe u

namespace QuadraticIncidence.InfinityChart

/-- The canonical zero-quotient projection identifies the entire original zero section. -/
theorem polynomial_zero_quotient_inclusion (R : Type u) [CommRing R] :
    source (Polynomial.X : Polynomial R) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) =
        inclusion (Polynomial.X : Polynomial R) := by
  rw [source, inclusion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change AdjoinRoot.of (Polynomial.X : Polynomial R) ((Polynomial.C r).eval 0) =
      AdjoinRoot.mk (Polynomial.X : Polynomial R) (Polynomial.C r)
    rw [Polynomial.eval_C]
    rfl
  · change AdjoinRoot.of (Polynomial.X : Polynomial R) (Polynomial.X.eval 0) =
      AdjoinRoot.mk (Polynomial.X : Polynomial R) Polynomial.X
    rw [Polynomial.eval_X, map_zero, AdjoinRoot.mk_self]

/-- The original affine-line zero square has a genuine simultaneous presentation.
No finite generating tuple, dimension, compactification, or section-correction
data are supplied by the caller. -/
theorem nonempty_polynomialZero_originalEtalePresentation
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.Smooth k R]
    (x : PrimeSpectrum (Polynomial R)) [x.asIdeal.IsMaximal]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))
    [Etale p] [QuasiCompact p] [IsSeparated p]
    (s : Spec (.of R) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (H : IsPullback s (𝟙 _) p
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))) :
    Nonempty (OriginalEtalePresentation k
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k R)))
      p (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)))
      (inclusion (Polynomial.X : Polynomial R))
      (source (Polynomial.X : Polynomial R) ≫ s) x) := by
  classical
  have hbase : Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial R))) := by
    rw [← Spec.map_comp]
    rfl
  rw [hbase]
  let : Algebra.Smooth R (Polynomial R) := {}
  let : Algebra.Smooth k (Polynomial R) := Algebra.Smooth.comp k R (Polynomial R)
  have hJ : Ideal.span ({Polynomial.X} : Set (Polynomial R)) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr Polynomial.X_ne_zero
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := Polynomial R)
  have hg : Algebra.adjoin k (Set.range (fun g : G => (g : Polynomial R))) = ⊤ := by
    convert hG using 1
    congr 1
    ext g
    simp
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := R))
  have hd' : Algebra.trdeg k (Polynomial R) = (d + 1 : ℕ) := by
    rw [← trdeg_add_eq k R (A := Polynomial R),
      Polynomial.trdeg_of_isDomain, hd, Nat.cast_add, Nat.cast_one]
  have : IsIso (source (Polynomial.X : Polynomial R)) := by
    have hp : (Polynomial.X - Polynomial.C (0 : R) : Polynomial R) = Polynomial.X := by
      rw [Polynomial.C_0, sub_zero]
    exact (congrArg (fun q : Polynomial R => IsIso (source q)) hp).mp
      (source_linear_isIso (0 : R))
  have hz := polynomial_zero_quotient_inclusion R
  have hs' : (source (Polynomial.X : Polynomial R) ≫ s) ≫ p =
      inclusion (Polynomial.X : Polynomial R) := by
    rw [Category.assoc, hs, hz]
  have H' : IsPullback (source (Polynomial.X : Polynomial R) ≫ s) (𝟙 _) p
      (inclusion (Polynomial.X : Polynomial R)) := by
    apply H.of_iso' (asIso (source (Polynomial.X : Polynomial R))) (Iso.refl _)
      (asIso (source (Polynomial.X : Polynomial R))) (Iso.refl _)
    · simp
    · simp
    · simp
    · simpa using hz
  apply nonempty_originalEtalePresentation k (Polynomial R) x
    (Ideal.span {Polynomial.X}) hJ (fun g : G => (g : Polynomial R)) hg d hd'
    p (Scheme.Opens.ι (X := Spec (.of (Polynomial R)))
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)))
    (source (Polynomial.X : Polynomial R) ≫ s) hs' H'
  · change Disjoint (Set.range (principalOpen (Polynomial.X : Polynomial R)).ι)
      (Set.range (inclusion (Polynomial.X : Polynomial R)))
    rw [Scheme.Opens.range_ι, range_inclusion_complement]
    exact disjoint_compl_right
  · intro y
    change y ∈ Set.range (principalOpen (Polynomial.X : Polynomial R)).ι ∨
      y ∈ Set.range (inclusion (Polynomial.X : Polynomial R))
    rw [Scheme.Opens.range_ι, range_inclusion_complement]
    exact em (y ∈ principalOpen (Polynomial.X : Polynomial R))

end QuadraticIncidence.InfinityChart
