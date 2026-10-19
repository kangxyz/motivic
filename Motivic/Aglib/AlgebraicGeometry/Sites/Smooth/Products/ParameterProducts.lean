/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.ParameterProduct
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Continuous parameter products on the smooth site

The endofunctor multiplying by a smooth parameter uses the literal relative
scheme product and its original scheme maps. It preserves existing pullbacks
and is continuous for the actual smooth Nisnevich topology. Consequently
precomposition preserves sheaves with values in arbitrary category universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- Multiplication by a fixed smooth parameter, using literal relative products. -/
def parameterProduct (T : SmoothSite S) : SmoothSite S ⥤ SmoothSite S where
  obj X := product X T
  map f := productMap f (𝟙 T)
  map_id X := productMap_id X T
  map_comp f g := by simpa using productMap_comp f g (𝟙 T) (𝟙 T)

@[simp] theorem parameterProduct_obj (T X : SmoothSite S) :
    (parameterProduct T).obj X = product X T := rfl

@[simp] theorem parameterProduct_map (T : SmoothSite S) {X Y : SmoothSite S}
    (f : X ⟶ Y) : (parameterProduct T).map f = productMap f (𝟙 T) := rfl

/-- The categorical product functor identifies with the actual relative products. -/
def categoricalParameterProductIso (T : SmoothSite S) :
    prod.functor.flip.obj T ≅ parameterProduct T :=
  NatIso.ofComponents (fun X ↦ categoricalProductIso X T)
    (fun f ↦ categoricalProductIso_naturality f (𝟙 T))

instance parameterProduct_preservesPullbacks (T : SmoothSite S) :
    PreservesLimitsOfShape WalkingCospan (parameterProduct T) := by
  let : PreservesLimitsOfShape WalkingCospan (prod.functor.flip.obj T) :=
    Limits.prodRight_preservesPullbacks T
  exact preservesLimitsOfShape_of_natIso (categoricalParameterProductIso T)

instance parameterProduct_isContinuous (T : SmoothSite S) :
    (parameterProduct T).IsContinuous (nisnevichTopology S) (nisnevichTopology S) := by
  let : (prod.functor.flip.obj T).IsContinuous
      (nisnevichTopology S) (nisnevichTopology S) :=
    Functor.prodRight_isContinuous (nisnevichPrecoverage S) T
  exact Functor.isContinuous_of_iso (categoricalParameterProductIso T)
    (nisnevichTopology S) (nisnevichTopology S)

/-- Restriction along the literal parameter product preserves sheaves without
restricting either universe of the coefficient category. -/
theorem parameterProduct_op_comp_isSheaf (T : SmoothSite S)
    {A : Type w} [Category.{v} A] (P : (SmoothSite S)ᵒᵖ ⥤ A)
    (hP : Presheaf.IsSheaf (nisnevichTopology S) P) :
    Presheaf.IsSheaf (nisnevichTopology S) ((parameterProduct T).op ⋙ P) :=
  (parameterProduct T).op_comp_isSheaf_of_isSheaf _ _ P hP

end AlgebraicGeometry.Scheme.SmoothSite
