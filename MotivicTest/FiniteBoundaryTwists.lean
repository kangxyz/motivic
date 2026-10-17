/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteBoundaryTwists

/-! # One finite-base shrink supplies all positive-twist generating sections -/

@[expose] public section
noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph

universe u

example
    (R : Type u) [CommRing R] (ι : Type u)
    {Z S : Scheme.{u}} (f : Z ⟶ S) [IsFinite f]
    (g : Z ⟶ ProjectiveSpace R ι) (s : S) :
    ∃ V : S.Opens, s ∈ V ∧
      ∃ e : (n : ℕ) →
          (Modules.pullback ((f ⁻¹ᵁ V).ι ≫ g)).obj (twistingSheaf R ι (n : ℤ)) ≅
            SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf,
      ∃ σ : (n : ℕ) →
          Γ((Modules.pullback ((f ⁻¹ᵁ V).ι ≫ g)).obj (twistingSheaf R ι (n : ℤ)), ⊤),
        ∀ n, (e n).hom.app ⊤ (σ n) = (1 : Γ((f ⁻¹ᵁ V).toScheme, ⊤)) ∧
          IsIso ((unitHomGlobalSectionsEquiv (f ⁻¹ᵁ V).toScheme
            ((Modules.pullback ((f ⁻¹ᵁ V).ι ≫ g)).obj
              (twistingSheaf R ι (n : ℤ)))).symm (σ n)) :=
  exists_base_open_positiveTwist_unitSections R ι f g s

#print axioms exists_base_open_positiveTwist_unitSections
#print axioms positiveTwistUnitSection_isIso
