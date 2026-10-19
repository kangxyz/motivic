/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Basic

/-!
# Scalar null-homotopies for one-element Koszul complexes

Multiplication by the defining scalar on the genuine two-term complex is
chain-homotopic to zero, with the identity as its only nonzero homotopy
component. Tensor scalar identities prepare transport to arbitrary finite
Koszul complexes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The defining scalar acts null-homotopically on its two-term complex. -/
noncomputable def singleScalarHomotopy (M : Type u) [AddCommGroup M] [Module R M] (a : R) :
    Homotopy (a • 𝟙 (singleComplex M a)) 0 := by
  let h : ∀ i j, (ComplexShape.down ℕ).Rel j i →
      ((singleComplex M a).X i ⟶ (singleComplex M a).X j) := fun i j hij => by
    have hij : i + 1 = j := hij
    subst j
    cases i with
    | zero => exact 𝟙 (ModuleCat.of R M)
    | succ n => exact 0
  have heq : a • 𝟙 (singleComplex M a) = Homotopy.nullHomotopicMap' h := by
    apply HomologicalComplex.Hom.ext
    funext n
    obtain (_ | _ | n) := n
    · rw [Homotopy.nullHomotopicMap'_f_of_not_rel_left
        (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by simp)]
      change a • 𝟙 (ModuleCat.of R M) = 𝟙 _ ≫ (singleComplex M a).d 1 0
      rw [Category.id_comp, singleComplex_d_one_zero]
      rfl
    · rw [Homotopy.nullHomotopicMap'_f
        (show (ComplexShape.down ℕ).Rel 2 1 from rfl)
        (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      change a • 𝟙 (ModuleCat.of R M) =
        ModuleCat.ofHom (LinearMap.lsmul R M a) ≫ 𝟙 (ModuleCat.of R M) +
          (0 : ModuleCat.of R M ⟶ (singleComplex M a).X 2) ≫
            (0 : (singleComplex M a).X 2 ⟶ ModuleCat.of R M)
      rw [Category.comp_id, zero_comp, add_zero]
      rfl
    · exact (isZero_zero (ModuleCat R)).eq_of_src _ _
  exact (Homotopy.ofEq heq).trans (Homotopy.nullHomotopy' h)

/-- Scalar action in the first tensor factor is scalar action on the total complex. -/
theorem tensorHom_scalar_left (K L : ChainComplex (ModuleCat R) ℕ) (a : R) :
    HomologicalComplex.tensorHom (a • 𝟙 K) (𝟙 L) =
      a • 𝟙 (HomologicalComplex.tensorObj K L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp [HomologicalComplex.tensorHom, Linear.comp_smul]

/-- Scalar action in the second tensor factor is scalar action on the total complex. -/
theorem tensorHom_scalar_right (K L : ChainComplex (ModuleCat R) ℕ) (a : R) :
    HomologicalComplex.tensorHom (𝟙 K) (a • 𝟙 L) =
      a • 𝟙 (HomologicalComplex.tensorObj K L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp [HomologicalComplex.tensorHom, Linear.comp_smul]

end ChainComplex.Koszul
