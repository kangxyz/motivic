/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.WholeAffineLineBaseSquareMaps
/-! # The retained target restricts the original overlap, not its coefficient sheaf -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.Hom
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] (ι : Type u)
  {X Y A C : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) (j : Y ⟶ C)
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]
  [SmoothOfRelativeDimension 1 ((pullback.fst p a ≫ j) ≫ (f ≫ toSpec R ι))]

abbrev boundaryBaseOriginalOverlapTarget :=
  RelativeCurvePencil.relativeTargetSite k (boundaryBaseFieldMap V t)
    (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)
    (boundaryBaseRetainedTarget (f ≫ toSpec R ι) V (pullback.fst p a ≫ j))

def boundaryBaseOriginalOverlapTargetRestriction :
    boundaryBaseOriginalOverlapTarget k R ι t p a f j V ⟶ originalOverlapSite k R t q p a :=
  SmoothSite.homMk (((pullback.fst p a ≫ j) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).ι (by
    change _ = (boundaryBaseRetainedTarget (f ≫ toSpec R ι) V (pullback.fst p a ≫ j) ≫
      (boundaryBaseProjectiveMap R ι f V ≫ toSpec Γ(V.toScheme, ⊤) ι)) ≫
        boundaryBaseFieldMap V t
    simp only [boundaryBaseProjectiveMap_toSpec, boundaryBaseFieldMap,
      Category.assoc, Iso.hom_inv_id_assoc, boundaryBaseRetainedTarget,
      boundaryBaseWholeMap_fst_assoc, morphismRestrict_ι_assoc]
    change _ = _ ≫ (pullback.fst p a ≫ j) ≫ (f ≫ toSpec R ι) ≫ t
    simp only [Category.assoc]
    have hjt := congrArg (fun z => z ≫ t) hj
    simp only [Category.assoc] at hjt
    rw [hjt]
    rfl)


@[reassoc] theorem boundaryBaseOriginalOverlapTargetRestriction_graph :
    boundaryBasePencilGraph k R ι t q p a f j hj U V (pullback.fst p a ≫ j)
      (𝟙 _) (Category.id_comp _) ≫
        boundaryBaseOriginalOverlapTargetRestriction k R ι t q p a f j hj V =
      boundaryBaseOverlapRestriction k R ι t q p a f j hj U V := by
  ext
  exact (boundaryBaseOverlapTarget_ι q p a U V (f ≫ toSpec R ι) j hj
    (pullback.fst p a ≫ j) (𝟙 _) (Category.id_comp _)).trans (Category.comp_id _)

end AlgebraicGeometry.Scheme.Hom
