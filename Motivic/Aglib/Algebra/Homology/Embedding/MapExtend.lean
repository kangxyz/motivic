/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-! # Applying a zero-preserving functor commutes with extension by zero -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂ w₁ w₂
namespace HomologicalComplex
variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasZeroMorphisms D]
  {ι : Type w₁} {ι' : Type w₂} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex C c) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Componentwise extension-by-zero comparison, with the original map on nonzero degrees. -/
def mapExtendXIso (i : Option ι) :
    F.obj (extend.X K i) ≅ extend.X ((F.mapHomologicalComplex c).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => F.mapZeroObject

/-- The component comparison preserves the original differential. -/
theorem mapExtendXIso_hom_d (i j : Option ι) :
    (mapExtendXIso K F i).hom ≫ extend.d ((F.mapHomologicalComplex c).obj K) i j =
      F.map (extend.d K i j) ≫ (mapExtendXIso K F j).hom := by
  cases i <;> cases j <;>
    simp [mapExtendXIso, extend.d, Functor.mapHomologicalComplex]

/-- An additive functor may be applied before or after extending a complex by zero. -/
def mapExtendIso (e : c.Embedding c') :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  Hom.isoOfComponents (fun i => mapExtendXIso K F (e.r i))
    (fun i j _ => mapExtendXIso_hom_d K F (e.r i) (e.r j))

/-- The comparison respects genuine maps of the original complexes. -/
@[reassoc]
theorem mapExtendIso_naturality {L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') :
    (F.mapHomologicalComplex c').map (extendMap φ e) ≫ (mapExtendIso L F e).hom =
      (mapExtendIso K F e).hom ≫ extendMap ((F.mapHomologicalComplex c).map φ) e := by
  ext i
  change F.map (extend.mapX φ (e.r i)) ≫ (mapExtendXIso L F (e.r i)).hom =
    (mapExtendXIso K F (e.r i)).hom ≫ extend.mapX ((F.mapHomologicalComplex c).map φ) (e.r i)
  have h (a : Option ι) :
      F.map (extend.mapX φ a) ≫ (mapExtendXIso L F a).hom =
        (mapExtendXIso K F a).hom ≫ extend.mapX ((F.mapHomologicalComplex c).map φ) a := by
    cases a <;> simp [mapExtendXIso, extend.mapX, Functor.mapHomologicalComplex]
  exact h _

/-- The comparison respects the actual natural transformation between coefficient functors. -/
@[reassoc]
theorem mapExtendIso_naturality_functor (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (τ : F ⟶ G) (e : c.Embedding c') :
    (NatTrans.mapHomologicalComplex τ c').app (K.extend e) ≫ (mapExtendIso K G e).hom =
      (mapExtendIso K F e).hom ≫ extendMap ((NatTrans.mapHomologicalComplex τ c).app K) e := by
  ext i
  change τ.app (extend.X K (e.r i)) ≫ (mapExtendXIso K G (e.r i)).hom =
    (mapExtendXIso K F (e.r i)).hom ≫
      extend.mapX ((NatTrans.mapHomologicalComplex τ c).app K) (e.r i)
  have h (a : Option ι) :
      τ.app (extend.X K a) ≫ (mapExtendXIso K G a).hom =
        (mapExtendXIso K F a).hom ≫
          extend.mapX ((NatTrans.mapHomologicalComplex τ c).app K) a := by
    cases a with
    | none => exact (Functor.map_isZero F (Limits.isZero_zero C)).eq_of_src _ _
    | some a => simp [mapExtendXIso, extend.X, extend.mapX, NatTrans.mapHomologicalComplex]
  exact h _

end HomologicalComplex
