/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Field
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FiniteGraphSections
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.BaseChangeIsomorphism

/-! # Fixed-source units for the actual relative projective twists -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Original finite-field-boundary units trivialize the actual relative twist on the whole
base-changed boundary, with its given coefficient-map square and without shrinking the source. -/
def fieldBoundaryRelativeTwistIso (k R : Type u) [Field k] [CommRing R]
    (f : k →+* R) (ι : Type u) {Z W : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (a : W ⟶ ProjectiveSpace R ι)
    (ha : a ≫ ProjectiveSpace.map f ι = b ≫ g) (n : ℕ) :
    (Modules.pullback a).obj (twistingSheaf R ι (n : ℤ)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  (Modules.pullback a).mapIso (twistingBaseChangeIso f ι (n : ℤ)).symm ≪≫
    (Modules.pullbackComp a (ProjectiveSpace.map f ι)).app (twistingSheaf k ι (n : ℤ)) ≪≫
    (Modules.pullbackCongr ha).app (twistingSheaf k ι (n : ℤ)) ≪≫
    fieldBoundaryTwistBaseChangeIso k ι g b n

/-- The precise coefficient sheaf used by the original finite-map section producer is globally
trivial on the full base-changed boundary, before choosing a Serre degree. -/
def fieldBoundaryRelativeCoefficientIso (k R : Type u) [Field k] [CommRing R]
    (f : k →+* R) (ι : Type u) {Z W C : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (a : C ⟶ ProjectiveSpace R ι) (z : W ⟶ C)
    (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g) (n : ℕ) :
    (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (n : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  boundaryTwistCoefficientIso a z (twistingSheaf R ι (n : ℤ)) ≪≫
    fieldBoundaryRelativeTwistIso k R f ι g b (z ≫ a) ha n

/-- An actual section and actual generating map for the original relative coefficient sheaf. -/
theorem exists_fieldBoundaryRelativeCoefficient_unitSection
    (k R : Type u) [Field k] [CommRing R]
    (f : k →+* R) (ι : Type u) {Z W C : Scheme.{u}}
    (g : Z ⟶ ProjectiveSpace k ι) [IsFinite (g ≫ toSpec k ι)]
    (b : W ⟶ Z) (a : C ⟶ ProjectiveSpace R ι) (z : W ⟶ C)
    (ha : (z ≫ a) ≫ ProjectiveSpace.map f ι = b ≫ g) (n : ℕ) :
    let Q := (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (n : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))
    ∃ σ : Γ(Q, ⊤), IsIso ((unitHomGlobalSectionsEquiv W Q).symm σ) := by
  let Q := (moduleTensorLeftFunctor W
    ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (n : ℤ))))).obj
      ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))
  let e : Q ≅ SheafOfModules.unit W.ringCatSheaf :=
    fieldBoundaryRelativeCoefficientIso k R f ι g b a z ha n
  refine ⟨(unitHomGlobalSectionsEquiv W Q) e.inv, ?_⟩
  rw [Equiv.symm_apply_apply]
  infer_instance

end AlgebraicGeometry.Scheme.CoherentGraph
