/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.Moving.OneSided
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Vanishing on an actual open immersion is vanishing on its original open image -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k] {S X : SmoothSite (Spec (.of k))}
  [IsAffine S.left] [IsAffine X.left]
local instance : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
local instance : IsNoetherian X.left := {}

/-- No sheaf condition is needed: the inverse of the original open-image isomorphism
transports zero to the literal original open subset. -/
theorem zero_on_open_image (P : PresheafWithTransfers.{w} k)
    (f : S ⟶ X) [IsOpenImmersion f.left]
    (s : P.sections (Cor.mk X)) (h : P.transfer ((Cor.graphFunctor k).map f) s = 0) :
    let O := f.left.opensRange
    let : IsAffine O.toScheme := isAffineOpen_opensRange f.left
    P.transfer ((Cor.graphFunctor k).map
      (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) s = 0 := by
  let O := f.left.opensRange
  let : IsAffine O.toScheme := isAffineOpen_opensRange f.left
  let T := SmoothSite.mk (O.ι ≫ X.hom)
  have hw : f.left ≫ X.hom = S.hom := f.w
  let g : T ⟶ S := SmoothSite.homMk f.left.isoOpensRange.inv (by
    change f.left.isoOpensRange.inv ≫ S.hom = O.ι ≫ X.hom
    rw [← hw, ← Category.assoc]
    simp only [Scheme.Hom.isoOpensRange_inv_comp]
    rfl)
  have hc : g ≫ f = SmoothSite.homMk (X := T) (Y := X) O.ι rfl := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.Hom.isoOpensRange_inv_comp f.left
  change P.transfer ((Cor.graphFunctor k).map (SmoothSite.homMk (X := T) (Y := X) O.ι rfl)) s = 0
  rw [← hc, Functor.map_comp, transfer_comp]
  change P.transfer ((Cor.graphFunctor k).map g)
    (P.transfer ((Cor.graphFunctor k).map f) s) = 0
  rw [h, map_zero]

end Motivic.PresheafWithTransfers
