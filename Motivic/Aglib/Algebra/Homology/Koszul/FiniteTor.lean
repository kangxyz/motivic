/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Actual Tor from finite regular-sequence Koszul resolutions

The proved projective resolution computes genuine categorical Tor. Tensoring
its ring-coefficient complex is explicitly identified with the finite Koszul
complex with arbitrary module coefficients. Regularity is required on the ring
for the Tor comparison, and on the coefficient module only for additional
positive-degree vanishing.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- Changing coefficient modules by an isomorphism changes the actual complex isomorphically. -/
noncomputable def coefficientIso {M N : ModuleCat R} (e : M ≅ N) :
    (s : List R) → coefficientComplex M s ≅ coefficientComplex N s
  | [] => (ChainComplex.single₀ (ModuleCat R)).mapIso e
  | a :: s => whiskerLeftIso (singleComplex R a) (coefficientIso e s)

/-- Tensoring on the left preserves the scalar multiplication morphisms. -/
theorem tensoringLeft_map_lsmul (M X : ModuleCat R) (a : R) :
    ((tensoringLeft (ModuleCat R)).obj M).map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul R (M ⊗ X) a) := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext (LinearMap.ext fun m => LinearMap.ext fun x => ?_)
  change m ⊗ₜ[R] (a • x) = a • (m ⊗ₜ[R] x)
  simp

/-- Tensoring the actual ring Koszul complex gives the actual coefficient complex. -/
noncomputable def tensorCoefficientIso (M : ModuleCat R) (s : List R) :
    mappedComplex ((tensoringLeft (ModuleCat R)).obj M) (chainComplex s) ≅
      coefficientComplex M s :=
  eqToIso (congrArg (mappedComplex ((tensoringLeft (ModuleCat R)).obj M))
    (coefficientComplex_ring s).symm) ≪≫
      coefficientMapIso ((tensoringLeft (ModuleCat R)).obj M)
        (fun a X => tensoringLeft_map_lsmul M X a) (ModuleCat.of R R) s ≪≫
          coefficientIso (ρ_ M) s

/-- Coefficient Koszul complexes vanish above the length of the input list. -/
theorem coefficient_isZero_X (M : ModuleCat R) (s : List R) (n : ℕ) (h : s.length < n) :
    IsZero ((coefficientComplex M s).X n) := by
  induction s generalizing n with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M n
      (by simpa using (Nat.ne_of_gt h))
  | cons a s ih =>
    exact tensor_isZero_X (singleComplex R a) (coefficientComplex M s) 1 s.length
      (single_isZero_X a) ih n (by simpa [Nat.add_comm] using h)

/-- Genuine categorical Tor is the homology of the constructed coefficient Koszul complex. -/
noncomputable def finiteTorIsoHomology (M : ModuleCat R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s)) ≅
      (coefficientComplex M s).homology n :=
  (finiteProjectiveResolution s hs).isoLeftDerivedObj
    ((tensoringLeft (ModuleCat R)).obj M) n ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
        (tensorCoefficientIso M s)

/-- Tor against the regular-sequence quotient vanishes above the sequence length. -/
theorem isZero_finiteTor_above_length (M : ModuleCat R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) (hn : s.length < n) :
    IsZero (((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) :=
  (HomologicalComplex.ExactAt.of_isZero (coefficient_isZero_X M s n hn)).isZero_homology.of_iso
    (finiteTorIsoHomology M s hs n)

/-- Additional regularity on the coefficient module kills all positive Tor. -/
theorem isZero_finiteTor_succ_of_weaklyRegular (M : ModuleCat R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s)
    (hM : RingTheory.Sequence.IsWeaklyRegular M s) (n : ℕ) :
    IsZero (((Tor (ModuleCat R) (n + 1)).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) :=
  (coefficient_exactAt_succ_of_weaklyRegular M s hM n).isZero_homology.of_iso
    (finiteTorIsoHomology M s hs (n + 1))

end ChainComplex.Koszul
