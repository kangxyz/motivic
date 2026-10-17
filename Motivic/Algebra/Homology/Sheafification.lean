/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Canonical sheafification of ordinary presheaf complexes

On an arbitrary site, with abelian coefficients and an actual `HasSheafify`
instance, `Motivic.Sheafification.functor` applies Mathlib's canonical
`presheafToSheaf` in every degree. The differential and every chain-map
component are the actual images under this functor. Its natural unit is the
ordinary sheafification unit degree by degree.

The sheafification functor is exact: the `HasSheafify` interface supplies
preservation of finite limits, and the sheafification adjunction supplies
preservation of colimits. Consequently the homology sheaf of the sheafified
complex is canonically the sheafification of its presheaf homology, naturally
in the complex, and sheafification preserves quasi-isomorphisms.

No exactness of the inclusion of sheaves into presheaves is asserted. These
are ordinary sheaves; transfers and the geometric motivic input are separate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Motivic.Sheafification

universe v u v' u' w

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A] [Abelian A]
variable (J : GrothendieckTopology C) [HasSheafify J A]
variable {ι : Type w} (c : ComplexShape ι)

/-- Degreewise canonical sheafification of actual presheaf complexes. -/
def functor : HomologicalComplex (Cᵒᵖ ⥤ A) c ⥤ HomologicalComplex (Sheaf J A) c :=
  (presheafToSheaf J A).mapHomologicalComplex c

/-- The underlying presheaf complex of a complex of sheaves. -/
def underlyingFunctor :
    HomologicalComplex (Sheaf J A) c ⥤ HomologicalComplex (Cᵒᵖ ⥤ A) c :=
  (sheafToPresheaf J A).mapHomologicalComplex c

variable {c}

/-- The canonical sheafified complex, with all differentials sheafified. -/
abbrev obj (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) :
    HomologicalComplex (Sheaf J A) c :=
  (functor J c).obj K

@[simp]
theorem obj_X (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) (i : ι) :
    (obj J K).X i = (presheafToSheaf J A).obj (K.X i) := rfl

@[simp]
theorem obj_d (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) (i j : ι) :
    (obj J K).d i j = (presheafToSheaf J A).map (K.d i j) := rfl

/-- The actual induced map of sheafified complexes. -/
abbrev map {K L : HomologicalComplex (Cᵒᵖ ⥤ A) c} (f : K ⟶ L) :
    obj J K ⟶ obj J L :=
  (functor J c).map f

@[simp]
theorem map_f {K L : HomologicalComplex (Cᵒᵖ ⥤ A) c} (f : K ⟶ L) (i : ι) :
    (map J f).f i = (presheafToSheaf J A).map (f.f i) := rfl

variable (c)

/-- The natural unit to the underlying presheaf complex of the sheafification. -/
def unit : 𝟭 (HomologicalComplex (Cᵒᵖ ⥤ A) c) ⟶
    functor J c ⋙ underlyingFunctor J c where
  app K :=
    { f i := toSheafify J (K.X i)
      comm' i j _ := (toSheafify_naturality J (K.d i j)).symm }
  naturality K L f := by
    ext i : 1
    exact toSheafify_naturality J (f.f i)

@[simp]
theorem unit_app_f (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) (i : ι) :
    ((unit J c).app K).f i = toSheafify J (K.X i) := rfl

/-- The counit comes from the actual sheafification adjunction in each degree. -/
def counit : underlyingFunctor J c ⋙ functor J c ⟶
    𝟭 (HomologicalComplex (Sheaf J A) c) where
  app K :=
    { f i := (sheafificationAdjunction J A).counit.app (K.X i)
      comm' i j _ := ((sheafificationAdjunction J A).counit.naturality (K.d i j)).symm }
  naturality K L f := by
    ext i : 1
    exact (sheafificationAdjunction J A).counit.naturality (f.f i)

/-- Degreewise sheafification is left adjoint to the inclusion of sheaf complexes. -/
def adjunction : functor (A := A) J c ⊣ underlyingFunctor J c where
  unit := unit J c
  counit := counit J c
  left_triangle_components K := by
    ext i : 1
    exact (sheafificationAdjunction J A).left_triangle_components (K.X i)
  right_triangle_components K := by
    ext i : 1
    exact (sheafificationAdjunction J A).right_triangle_components (K.X i)

/-- Exactness of ordinary sheafification follows from its left-exact left adjoint. -/
theorem preservesHomology : (presheafToSheaf J A).PreservesHomology := inferInstance

variable {c}

/-- Canonical identification of sheafified homology, in every degree and complex shape. -/
def homologyIso (K : HomologicalComplex (Cᵒᵖ ⥤ A) c) (i : ι) :
    (obj J K).homology i ≅ (presheafToSheaf J A).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (presheafToSheaf J A)

@[reassoc]
theorem homologyIso_hom_naturality {K L : HomologicalComplex (Cᵒᵖ ⥤ A) c}
    (f : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap (map J f) i ≫ (homologyIso J L i).hom =
      (homologyIso J K i).hom ≫
        (presheafToSheaf J A).map (HomologicalComplex.homologyMap f i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ c i).map f) (presheafToSheaf J A)

/-- The homology comparison is an actual natural isomorphism of functors. -/
def homologyFunctorIso (i : ι) :
    functor J c ⋙ HomologicalComplex.homologyFunctor (Sheaf J A) c i ≅
      HomologicalComplex.homologyFunctor (Cᵒᵖ ⥤ A) c i ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun K => homologyIso J K i)
    (fun f => homologyIso_hom_naturality J f i)

/-- Canonical sheafification sends genuine quasi-isomorphisms to quasi-isomorphisms. -/
instance map_quasiIso {K L : HomologicalComplex (Cᵒᵖ ⥤ A) c}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (map J f) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology f (presheafToSheaf J A)

end Motivic.Sheafification
