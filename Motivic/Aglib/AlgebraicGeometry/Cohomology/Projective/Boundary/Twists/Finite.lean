/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteBaseNeighborhood

/-!
# Uniform unit sections of positive boundary twists

One trivialization of the actual restricted O(1) supplies trivializations
of every positive twist on the same open. Twist multiplication and pullback
tensor comparisons are the existing native maps.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- A fixed trivialization of the pulled-back O(1) trivializes every O(n),
without shrinking the source again when n changes. -/
def positiveTwistUnitIso (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι)
    (e₁ : (Modules.pullback g).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    (n : ℕ) → (Modules.pullback g).obj (twistingSheaf R ι (n : ℤ)) ≅
      SheafOfModules.unit Z.ringCatSheaf
  | 0 => (Modules.pullback g).mapIso (twistingZeroIso R ι) ≪≫ pullbackUnitIso g
  | n + 1 => by
      let := Modules.Pullback.Tensor.pullbackTensorMap_isIso g (twistingSheaf R ι (n : ℤ))
        (twistingSheaf R ι 1)
      exact (Modules.pullback g).mapIso
          (eqToIso (congrArg (twistingSheaf R ι) (Nat.cast_add n 1))) ≪≫
        ((Modules.pullback g).mapIso (twistingTensorIso R ι (n : ℤ) 1)).symm ≪≫
        asIso (pullbackTensorMap g (twistingSheaf R ι (n : ℤ)) (twistingSheaf R ι 1)) ≪≫
        tensorSheafIso Z (positiveTwistUnitIso R ι g e₁ n) e₁ ≪≫
        tensorSheafLeftUnit Z (SheafOfModules.unit Z.ringCatSheaf)

/-- The distinguished actual unit section of the positive twist. -/
def positiveTwistUnitSection (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι)
    (e₁ : (Modules.pullback g).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) :
    Γ((Modules.pullback g).obj (twistingSheaf R ι (n : ℤ)), ⊤) :=
  (positiveTwistUnitIso R ι g e₁ n).inv.app ⊤ (1 : Γ(Z, ⊤))

/-- Its coefficient is literally one under the constructed full-source
trivialization; this is a generating section, not a possibly vanishing lift. -/
theorem positiveTwistUnitSection_coefficient (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι)
    (e₁ : (Modules.pullback g).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) :
    (positiveTwistUnitIso R ι g e₁ n).hom.app ⊤
      (positiveTwistUnitSection R ι g e₁ n) = (1 : Γ(Z, ⊤)) := by
  simpa only [positiveTwistUnitSection, Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Modules.Hom.id_app, ConcreteCategory.id_apply] using
      congrArg (fun f => f.app ⊤ (1 : Γ(Z, ⊤))) (positiveTwistUnitIso R ι g e₁ n).inv_hom_id

/-- The distinguished section is a genuine basis: its original unit-to-
module map is an isomorphism, not merely a section nonzero at some points. -/
theorem positiveTwistUnitSection_isIso (R : Type u) [CommRing R] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace R ι)
    (e₁ : (Modules.pullback g).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit Z.ringCatSheaf) (n : ℕ) :
    IsIso ((unitHomGlobalSectionsEquiv Z
      ((Modules.pullback g).obj (twistingSheaf R ι (n : ℤ)))).symm
        (positiveTwistUnitSection R ι g e₁ n)) := by
  have he : (unitHomGlobalSectionsEquiv Z
      ((Modules.pullback g).obj (twistingSheaf R ι (n : ℤ)))).symm
        (positiveTwistUnitSection R ι g e₁ n) =
      (positiveTwistUnitIso R ι g e₁ n).inv := by
    apply (unitHomGlobalSectionsEquiv Z _).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.CoherentGraph

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- For a finite boundary over a base, shrink once at the chosen basepoint
using O(1). All nonnegative twists then have actual generating sections on
that same full inverse-image boundary, before any Serre bound is selected. -/
theorem exists_base_open_positiveTwist_unitSections
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
              (twistingSheaf R ι (n : ℤ)))).symm (σ n)) := by
  let L := Modules.Invertible.pullbackLineBundle g (twistingLineBundle R ι 1)
  obtain ⟨V, hs, ⟨eV⟩⟩ := Modules.Invertible.exists_base_open_unitIso_of_isFinite f s L
  let W := f ⁻¹ᵁ V
  let e₁ : (Modules.pullback (W.ι ≫ g)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι g).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback g).obj (twistingSheaf R ι 1)) ≪≫ eV
  exact ⟨V, hs, positiveTwistUnitIso R ι (W.ι ≫ g) e₁,
    positiveTwistUnitSection R ι (W.ι ≫ g) e₁,
    fun n => ⟨positiveTwistUnitSection_coefficient R ι (W.ι ≫ g) e₁ n,
      positiveTwistUnitSection_isIso R ι (W.ι ≫ g) e₁ n⟩⟩

end AlgebraicGeometry.Scheme.CoherentGraph
