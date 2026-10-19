/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatComplexTensorAcyclic
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# The actual tensor total with a module in degree zero

The degree `(0,n)` summand inclusions identify the actual signed total
`Tot(single M ⊗ G)` with the ordinary complex obtained by applying `M ⊗ -`
to `G`. This gives a direct bridge to mathlib's one-sided Tor computation on
a genuine projective resolution, without changing the complex or assuming
flatness of the coefficient module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
  (G : ChainComplex (ModuleCat.{u} R) ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual `(0,n)` tensor summands form the ordinary tensor complex. -/
noncomputable def flatComplexTensorSingleInclusion :
    ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj G ⟶
      mapBifunctor ((ChainComplex.single₀ (ModuleCat R)).obj M) G
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) where
  f n := ιMapBifunctor ((ChainComplex.single₀ (ModuleCat R)).obj M) G
    (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) 0 n n (by simp)
  comm' n m h := by
    obtain rfl := h
    rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
      mapBifunctor.ι_D₂,
      mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp), zero_add,
      mapBifunctor.d₂_eq _ _ _ _ 0
        (show (ComplexShape.down ℕ).Rel (m + 1) m from rfl) m (by simp)]
    exact one_smul ℤˣ _

/-- Each term of the canonical summand inclusion is an isomorphism. -/
theorem flatComplexTensorSingleInclusion_isIso_f (n : ℕ) :
    IsIso ((flatComplexTensorSingleInclusion M G).f n) := by
  let K := (((curriedTensor (ModuleCat R)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
    ((ChainComplex.single₀ (ModuleCat R)).obj M)).obj G
  refine ⟨⟨firstQuadrantπ K n 0 n, ?_, ?_⟩⟩
  · exact firstQuadrant_ι_π K 0 n n (by simp)
  · apply HomologicalComplex₂.total.hom_ext
    intro i j h
    change i + j = n at h
    cases i with
    | zero =>
        have hj : j = n := by omega
        subst j
        change K.ιTotal (ComplexShape.down ℕ) 0 n n h ≫
          firstQuadrantπ K n 0 n ≫ K.ιTotal (ComplexShape.down ℕ) 0 n n h =
            K.ιTotal (ComplexShape.down ℕ) 0 n n h ≫ 𝟙 _
        rw [firstQuadrant_ι_π_assoc, Category.comp_id]
    | succ i =>
        have hz : IsZero ((K.X (i + 1)).X j) :=
          (tensorRight (G.X j)).map_isZero
            (isZero_single_obj_X (ComplexShape.down ℕ) 0 M (i + 1) (by omega))
        exact hz.eq_of_src _ _

/-- Totalizing a degree-zero first factor is the ordinary tensor functor on complexes. -/
noncomputable def flatComplexTensorSingleIso :
    mapBifunctor ((ChainComplex.single₀ (ModuleCat R)).obj M) G
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) ≅
      ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj G := by
  letI (n : ℕ) : IsIso ((flatComplexTensorSingleInclusion M G).f n) :=
    flatComplexTensorSingleInclusion_isIso_f M G n
  letI := HomologicalComplex.Hom.isIso_of_components (flatComplexTensorSingleInclusion M G)
  exact (asIso (flatComplexTensorSingleInclusion M G)).symm

/-- The inverse is precisely the canonical total-complex summand inclusion. -/
@[simp]
theorem flatComplexTensorSingleIso_inv :
    (flatComplexTensorSingleIso M G).inv = flatComplexTensorSingleInclusion M G := rfl

/-- The actual total with one degree-zero factor computes the actual one-sided Tor. -/
noncomputable def flatComplexTensorSingleTorIso {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor ((ChainComplex.single₀ (ModuleCat R)).obj M) P.complex
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)).homology n ≅
      (((Tor (ModuleCat R) n).obj M).obj N) :=
  (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (flatComplexTensorSingleIso M P.complex) ≪≫
    (P.isoLeftDerivedObj (tensorLeft M) n).symm

end ModuleCat.TorComparison
