/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointNeighborhood
public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePersistentMarkedSection

/-! # Actual open refinements on the existing field-point neighborhood index -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}} (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)

/-- An open containing the marked field image supplies a refinement in the original point fiber.
No new neighborhood category or assumed cofinality is introduced. -/
theorem exists_point_open_refinement (V : FiniteEtaleSite S) [IsNoetherian V.left]
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V) (O : V.left.Opens)
    (hO : Set.range (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left ⊆ (O : Set V.left)) :
    ∃ a' : (relativeFieldPoint b K (𝟙 _)).fiber.obj (testOpenObject V O),
      (relativeFieldPoint b K (𝟙 _)).fiber.map (testOpenInclusion V O) a' = a := by
  let t := relativeFieldPointFiberEquiv b K (𝟙 _) V a
  have hr : Set.range t.left ⊆ Set.range O.ι := by
    simpa only [Scheme.Opens.range_ι] using hO
  let l := IsOpenImmersion.lift O.ι t.left hr
  have hl : l ≫ O.ι = t.left := IsOpenImmersion.lift_fac O.ι t.left hr
  let t' : Over.mk (𝟙 _ ≫ b) ⟶
      (MorphismProperty.Over.forget _ _ S).obj (testOpenObject V O) :=
    Over.homMk l (by
      change l ≫ (O.ι ≫ V.hom) = 𝟙 _ ≫ b
      rw [← Category.assoc, hl]
      exact Over.w t)
  refine ⟨(relativeFieldPointFiberEquiv b K (𝟙 _) (testOpenObject V O)).symm t', ?_⟩
  apply (relativeFieldPointFiberEquiv b K (𝟙 _) V).injective
  rw [relativeFieldPointFiberEquiv_naturality, Equiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  exact hl

/-- For a field-valued marker, containing its one image point is enough. -/
theorem exists_point_open_refinement_of_mem (V : FiniteEtaleSite S) [IsNoetherian V.left]
    (a : (relativeFieldPoint b K (𝟙 _)).fiber.obj V) (p : Spec (.of K))
    (O : V.left.Opens)
    (hO : (relativeFieldPointFiberEquiv b K (𝟙 _) V a).left p ∈ O) :
    ∃ a' : (relativeFieldPoint b K (𝟙 _)).fiber.obj (testOpenObject V O),
      (relativeFieldPoint b K (𝟙 _)).fiber.map (testOpenInclusion V O) a' = a := by
  apply exists_point_open_refinement K b V a O
  rintro y ⟨p', rfl⟩
  have hp : (p' : Spec (.of K)) = p :=
    Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [hp]
  exact hO

end Motivic.FiniteEtaleSite
