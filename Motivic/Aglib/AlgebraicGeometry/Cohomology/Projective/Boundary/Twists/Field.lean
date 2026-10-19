/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Finite
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFiber

/-! # Global finite-field-boundary twist units without shrinking any source

A single unit trivialization on the full finite boundary over a field supplies all twists
and all their base changes. In particular the fixed affine-line open need not be shrunk.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The whole finite scheme over a field has a unit trivialization for every line bundle. -/
theorem finiteFieldLineBundle_trivial (k : Type u) [Field k]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsFinite f]
    (L : Invertible.LineBundle Z) :
    Nonempty (L.val ≅ SheafOfModules.unit Z.ringCatSheaf) := by
  let : IsAffine Z := isAffine_of_isAffineHom f
  let : Finite Z := Set.finite_univ_iff.mp (by
    simpa using f.finite_preimage (Set.finite_univ : (Set.univ : Set (Spec (.of k))).Finite))
  exact Invertible.finiteAffineLineBundle_trivial Z L

/-- Choose one global boundary O(1) unit, before selecting any Serre degree. -/
def fieldBoundaryTwistOneIso (k : Type u) [Field k] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)] :
    (Modules.pullback g).obj (twistingSheaf k ι 1) ≅ SheafOfModules.unit Z.ringCatSheaf :=
  (finiteFieldLineBundle_trivial k (g ≫ toSpec k ι)
    (Invertible.pullbackLineBundle g (twistingLineBundle k ι 1))).some

/-- All nonnegative twists are globally trivial on the original entire finite boundary. -/
def fieldBoundaryTwistIso (k : Type u) [Field k] (ι : Type u)
    {Z : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)] (n : ℕ) :
    (Modules.pullback g).obj (twistingSheaf k ι (n : ℤ)) ≅ SheafOfModules.unit Z.ringCatSheaf :=
  positiveTwistUnitIso k ι g (fieldBoundaryTwistOneIso k ι g) n

/-- Pull the same target-boundary units to any source product, without any source shrink. -/
def fieldBoundaryTwistIso_baseChange (k : Type u) [Field k] (ι : Type u)
    {Z W : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (h : W ⟶ Z) (n : ℕ) :
    (Modules.pullback (h ≫ g)).obj (twistingSheaf k ι (n : ℤ)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  ((Modules.pullbackComp h g).app (twistingSheaf k ι (n : ℤ))).symm ≪≫
    (Modules.pullback h).mapIso (fieldBoundaryTwistIso k ι g n) ≪≫ pullbackUnitIso h

/-- The actual global generating section after arbitrary source base change. -/
def fieldBoundaryTwistSection_baseChange (k : Type u) [Field k] (ι : Type u)
    {Z W : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (h : W ⟶ Z) (n : ℕ) :
    Γ((Modules.pullback (h ≫ g)).obj (twistingSheaf k ι (n : ℤ)), ⊤) :=
  (fieldBoundaryTwistIso_baseChange k ι g h n).inv.app ⊤ (1 : Γ(W, ⊤))

/-- Its coefficient is exactly one on the entire source, with no neighborhood shrink. -/
theorem fieldBoundaryTwistSection_baseChange_coefficient
    (k : Type u) [Field k] (ι : Type u)
    {Z W : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (h : W ⟶ Z) (n : ℕ) :
    (fieldBoundaryTwistIso_baseChange k ι g h n).hom.app ⊤
      (fieldBoundaryTwistSection_baseChange k ι g h n) = (1 : Γ(W, ⊤)) := by
  simpa only [fieldBoundaryTwistSection_baseChange, Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, Modules.Hom.id_app, ConcreteCategory.id_apply] using
      congrArg (fun f => f.app ⊤ (1 : Γ(W, ⊤)))
        (fieldBoundaryTwistIso_baseChange k ι g h n).inv_hom_id

/-- The pulled section defines an isomorphism from the original structure sheaf. -/
theorem fieldBoundaryTwistSection_baseChange_isIso
    (k : Type u) [Field k] (ι : Type u)
    {Z W : Scheme.{u}} (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (h : W ⟶ Z) (n : ℕ) :
    IsIso ((unitHomGlobalSectionsEquiv W
      ((Modules.pullback (h ≫ g)).obj (twistingSheaf k ι (n : ℤ)))).symm
        (fieldBoundaryTwistSection_baseChange k ι g h n)) := by
  have he : (unitHomGlobalSectionsEquiv W
      ((Modules.pullback (h ≫ g)).obj (twistingSheaf k ι (n : ℤ)))).symm
        (fieldBoundaryTwistSection_baseChange k ι g h n) =
      (fieldBoundaryTwistIso_baseChange k ι g h n).inv := by
    apply (unitHomGlobalSectionsEquiv W _).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.CoherentGraph
