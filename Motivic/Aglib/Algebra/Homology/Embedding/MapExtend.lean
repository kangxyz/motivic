/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Embedding.MapExtend
public import Mathlib.Algebra.Homology.Additive

/-! # Functor naturality of the canonical extension-by-zero comparison

The original comparison and its complex naturality are supplied by pinned Aglib.
-/
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

/-- The comparison respects the actual natural transformation between coefficient functors. -/
@[reassoc]
theorem mapExtendIso_naturality_functor (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (τ : F ⟶ G) (e : c.Embedding c') :
    (NatTrans.mapHomologicalComplex τ c').app (K.extend e) ≫ (mapExtendIso K G e).hom =
      (mapExtendIso K F e).hom ≫ extendMap ((NatTrans.mapHomologicalComplex τ c).app K) e := by
  ext i
  change τ.app (extend.X K (e.r i)) ≫ (extend.mapXIso K G (e.r i)).hom =
    (extend.mapXIso K F (e.r i)).hom ≫
      extend.mapX ((NatTrans.mapHomologicalComplex τ c).app K) (e.r i)
  have h (a : Option ι) :
      τ.app (extend.X K a) ≫ (extend.mapXIso K G a).hom =
        (extend.mapXIso K F a).hom ≫
          extend.mapX ((NatTrans.mapHomologicalComplex τ c).app K) a := by
    cases a with
    | none => exact (Functor.map_isZero F (Limits.isZero_zero C)).eq_of_src _ _
    | some a => simp [extend.mapXIso, extend.X, extend.mapX, NatTrans.mapHomologicalComplex]
  exact h _


end HomologicalComplex
