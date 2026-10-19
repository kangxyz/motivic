/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Pair.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# The actual projective resolution for a regular pair

The augmentation of the two-element Koszul complex is the quotient map to
`M / range(d₁)`. It is proved to be a quasi-isomorphism when the pair is
regular on `M`. For projective `M`, its terms are projective, so this gives
an actual `ProjectiveResolution`, including in particular the free resolution
of `R / (a,b)`. These proofs do not posit a resolution or its exactness.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M] (a b : R)

/-- The literal quotient map from degree zero to degree-zero Koszul homology. -/
def augmentationMap : ModuleCat.of R M ⟶ ModuleCat.of R (H₀ M a b) :=
  ModuleCat.ofHom (LinearMap.range (d₁ M a b)).mkQ

@[reassoc]
theorem d_one_zero_augmentationMap :
    (chainComplex M a b).d 1 0 ≫ augmentationMap M a b = 0 :=
  ModuleCat.hom_ext (LinearMap.exact_map_mkQ_range (d₁ M a b)).linearMap_comp_eq_zero

/-- The actual augmentation chain map to the quotient in degree zero. -/
noncomputable def augmentation :
    chainComplex M a b ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj
      (ModuleCat.of R (H₀ M a b)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨augmentationMap M a b, d_one_zero_augmentationMap M a b⟩

@[simp]
theorem augmentation_f_zero : (augmentation M a b).f 0 = augmentationMap M a b :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation is exact in degree zero, without any regularity assumption. -/
theorem augmentation_exact :
    (ShortComplex.mk ((chainComplex M a b).d 1 0) (augmentationMap M a b)
      (d_one_zero_augmentationMap M a b)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact LinearMap.exact_map_mkQ_range (d₁ M a b)

instance augmentationMap_epi : Epi (augmentationMap M a b) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- The quotient augmentation always induces an isomorphism on degree-zero homology. -/
theorem augmentation_quasiIsoAt_zero : QuasiIsoAt (augmentation M a b) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
  · exact ⟨augmentation_exact M a b, augmentationMap_epi M a b⟩
  · exact (chainComplex M a b).shape _ _ (by simp)
  · rfl
  · rfl

/-- All positive degrees of the literal augmented Koszul complex are exact for a regular pair. -/
theorem exactAt_succ_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b) (n : ℕ) :
    (chainComplex M a b).ExactAt (n + 1) := by
  obtain (_ | _ | n) := n
  · exact exactAt_one_of_regular M a b ha hb
  · exact exactAt_two_of_regular M a b ha
  · exact exactAt_add_three M a b n

/-- Regularity proves that the actual augmentation is a quasi-isomorphism. -/
theorem augmentation_quasiIso_of_regular (ha : IsSMulRegular M a)
    (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    QuasiIso (augmentation M a b) := by
  constructor
  intro n
  cases n with
  | zero => exact augmentation_quasiIsoAt_zero M a b
  | succ n =>
    rw [quasiIsoAt_iff_exactAt' _ _
      (ChainComplex.exactAt_succ_single_obj _ _)]
    exact exactAt_succ_of_regular M a b ha hb n

instance chainComplex_projective [Module.Projective R M] (n : ℕ) :
    CategoryTheory.Projective ((chainComplex M a b).X n) := by
  obtain (_ | _ | _ | n) := n
  · change CategoryTheory.Projective (ModuleCat.of R M)
    infer_instance
  · change CategoryTheory.Projective (ModuleCat.of R (M × M))
    infer_instance
  · change CategoryTheory.Projective (ModuleCat.of R M)
    infer_instance
  · exact IsZero.projective (isZero_zero _)

/-- The constructed Koszul projective resolution for a regular pair on a projective module.
Specializing `M = R` gives the length-two free resolution of the two-generated quotient. -/
noncomputable def projectiveResolution [Module.Projective R M]
    (ha : IsSMulRegular M a) (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    CategoryTheory.ProjectiveResolution (ModuleCat.of R (H₀ M a b)) where
  complex := chainComplex M a b
  π := augmentation M a b
  quasiIso := augmentation_quasiIso_of_regular M a b ha hb

@[simp]
theorem projectiveResolution_complex [Module.Projective R M]
    (ha : IsSMulRegular M a) (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    (projectiveResolution M a b ha hb).complex = chainComplex M a b := rfl

@[simp]
theorem projectiveResolution_π [Module.Projective R M]
    (ha : IsSMulRegular M a) (hb : IsSMulRegular (PrincipalQuotient M a) b) :
    (projectiveResolution M a b ha hb).π = augmentation M a b := rfl

end Module.KoszulPair
