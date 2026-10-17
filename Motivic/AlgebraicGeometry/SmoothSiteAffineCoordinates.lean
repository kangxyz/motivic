/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusDivisorNaturality

/-! # Natural actual affine coordinates on the smooth site -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.AffineTorusPolynomialPresentation

universe u

namespace Motivic.SmoothSiteAffineCoordinates

variable {k : Type u} [Field k]

/-- Scalars act through the original structure morphism on actual global sections. -/
def scalarMap (X : SmoothSite (Spec (.of k))) : k →+* Γ(X.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop).hom

/-- The actual global-section algebra, not a chosen presentation. -/
@[instance_reducible] def sectionsAlgebra (X : SmoothSite (Spec (.of k))) :
    Algebra k Γ(X.left, ⊤) := (scalarMap X).toAlgebra

attribute [local instance] sectionsAlgebra

/-- Ordinary restriction of sections is an algebra map for these original actions. -/
def sectionsMap {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    Γ(Y.left, ⊤) →ₐ[k] Γ(X.left, ⊤) where
  __ := f.left.appTop.hom
  commutes' r := by
    have he : Y.hom.appTop ≫ f.left.appTop = X.hom.appTop := by
      rw [← Scheme.Hom.comp_appTop, MorphismProperty.Over.w]
    exact congrArg (fun g => g ((Scheme.ΓSpecIso (.of k)).inv r)) he

variable (X : SmoothSite (Spec (.of k))) [IsAffine X.left]

/-- The affine global-section algebra of the original smooth scheme is smooth. -/
instance sectionsSmooth : Algebra.Smooth k Γ(X.left, ⊤) := by
  change (scalarMap X).Smooth
  dsimp only [scalarMap]
  rw [CommRingCat.hom_comp, RingHom.Smooth.respectsIso.cancel_left_isIso]
  simpa [Scheme.Hom.appTop, Scheme.Hom.appLE] using X.hom.smooth_appLE
    (isAffineOpen_top (Spec (.of k))) (isAffineOpen_top X.left) (by simp)

/-- Actual affine coordinates are noetherian. -/
instance sectionsNoetherian : IsNoetherianRing Γ(X.left, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X.left⟩

/-- The canonical affine scheme comparison preserves the original base map. -/
theorem isoSpec_inv_base :
    X.left.isoSpec.inv ≫ X.hom = baseMap k Γ(X.left, ⊤) := by
  rw [← Scheme.isoSpec_inv_naturality (show X.left ⟶ Spec (.of k) from X.hom),
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- Canonical affine coordinates as an isomorphism in the actual smooth site. -/
def affineIso : affineSite k Γ(X.left, ⊤) ≅ X where
  hom := SmoothSite.homMk X.left.isoSpec.inv (isoSpec_inv_base X)
  inv := SmoothSite.homMk X.left.isoSpec.hom (by
    apply (cancel_epi X.left.isoSpec.inv).mp
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (isoSpec_inv_base X).symm)
  hom_inv_id := by apply MorphismProperty.Over.Hom.ext; exact X.left.isoSpec.inv_hom_id
  inv_hom_id := by apply MorphismProperty.Over.Hom.ext; exact X.left.isoSpec.hom_inv_id

@[simp] theorem affineIso_hom_left : (affineIso X).hom.left = X.left.isoSpec.inv := rfl
@[simp] theorem affineIso_inv_left : (affineIso X).inv.left = X.left.isoSpec.hom := rfl

variable {X} {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]

/-- Canonical affine coordinates retain every actual ordinary morphism. -/
@[reassoc] theorem affineIso_naturality (f : X ⟶ Y) :
    affineMorphism (sectionsMap f) ≫ (affineIso Y).hom = (affineIso X).hom ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.isoSpec_inv_naturality f.left

end Motivic.SmoothSiteAffineCoordinates
