/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.SourceTargetBoundaryAffineNeighborhood

/-!
# The literal two-localization source and target affine ambients

This is the unchanged output predicate for the existing full-boundary affine
ambient supplier. It keeps both localization elements, the actual nested
pullbacks, both whole boundary schemes, and their exact factorization maps.

Intended upstream module: `SourceTargetFullAffineAmbients` in
`Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary`.
Current consumer: the fixed-boundary adapter in
`Normalization.Compactification.RelativeAffineLine.FixedThickenedBoundaryAffineAmbients`.

The normalization wrapper imports this declaration through its fixed-witness
adapter; there is only one implementation of the predicate.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The literal two-localization output of the source/target ambient supplier.
The boundary inputs are whole closed schemes, not reduced supports. -/
def SourceTargetFullBoundaryAffineAmbients
    (R : Type u) [CommRing R] {C B Z : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) (b : B ⟶ C)
    (z : Z ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) : Prop :=
    ∃ r : R, r ≠ 0 ∧
      let S := Localization.Away r
      let m₁ := ProjectiveSpace.map (algebraMap R S) (ULift.{u} (Fin 2))
      let f₁ := pullback.snd f m₁
      let b₁ : pullback (b ≫ f) m₁ ⟶ pullback f m₁ :=
        pullback.lift (pullback.fst (b ≫ f) m₁ ≫ b)
          (pullback.snd (b ≫ f) m₁) (by simp [Category.assoc, pullback.condition])
      let z₁ := pullback.snd z m₁
      ∃ s : S, s ≠ 0 ∧
        let m₂ := ProjectiveSpace.map (algebraMap S (Localization.Away s))
          (ULift.{u} (Fin 2))
        let t₂ := pullback.fst (𝟙 (ProjectiveSpace S (ULift.{u} (Fin 2)))) m₂
        let c₂ := pullback.fst f₁ t₂
        let z₂ := pullback.lift (pullback.fst (z₁ ≫ 𝟙 _) m₂ ≫ z₁)
          (pullback.snd (z₁ ≫ 𝟙 _) m₂) (by
            simpa only [Category.assoc, Category.comp_id] using
              (pullback.condition (f := z₁ ≫ 𝟙 _) (g := m₂)))
        ∃ U : (pullback f₁ t₂).Opens,
          ∃ V : (pullback (𝟙 (ProjectiveSpace S (ULift.{u} (Fin 2)))) m₂).Opens,
            IsAffineOpen U ∧ IsAffineOpen V ∧
            (∃ u : pullback b₁ c₂ ⟶ U.toScheme,
              u ≫ U.ι = pullback.snd b₁ c₂) ∧
            (∃ v : pullback (z₁ ≫ 𝟙 _) m₂ ⟶ V.toScheme, v ≫ V.ι = z₂)

end AlgebraicGeometry.ProjectiveSpace
