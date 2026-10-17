/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteUnits
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Detecting ordinary sheaf isomorphisms on actual affine smooth objects -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.SmoothSite

variable {S : Scheme.{u}} [IsAffine S]

/-- A sieve containing all affine-source arrows covers, by the genuine affine open cover. -/
theorem sieve_mem_of_affine_arrows (X : SmoothSite S) (T : Sieve X)
    (h : ∀ (U : SmoothSite S) [IsAffine U.left] (f : U ⟶ X), T f) :
    T ∈ nisnevichTopology S X := by
  let U (i : X.left.affineCover.I₀) : SmoothSite S :=
    mk (X.left.affineCover.f i ≫ X.hom)
  let f (i : X.left.affineCover.I₀) : U i ⟶ X :=
    homMk (X.left.affineCover.f i) rfl
  apply (mem_nisnevichTopology_iff).mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · change (Presieve.ofArrows U f).map (forgetScheme S) ∈ Nisnevich.precoverage X.left
    rw [Presieve.map_ofArrows]
    exact Nisnevich.zariskiPrecoverage_le_precoverage _ X.left.affineCover.mem₀
  · rw [Presieve.ofArrows_le_iff]
    intro i
    let : IsAffine (U i).left := by dsimp [U]; infer_instance
    exact h (U i) (f i)

/-- An ordinary Nisnevich sheaf map is an isomorphism if its actual affine sections are. -/
theorem isIso_of_affine_app
    {F G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : ∀ (X : SmoothSite S) [IsAffine X.left], IsIso (φ.hom.app (op X))) :
    IsIso φ := by
  have hi : Presheaf.IsLocallyInjective (nisnevichTopology S) φ.hom := by
    constructor
    intro X x y hxy
    apply sieve_mem_of_affine_arrows
    intro U _ f
    have := h U
    apply (ConcreteCategory.bijective_of_isIso (φ.hom.app (op U))).injective
    change φ.hom.app (op U) (F.obj.map f.op x) =
      φ.hom.app (op U) (F.obj.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  have hs : Presheaf.IsLocallySurjective (nisnevichTopology S) φ.hom := by
    constructor
    intro X x
    apply sieve_mem_of_affine_arrows
    intro U _ f
    have := h U
    exact (ConcreteCategory.bijective_of_isIso (φ.hom.app (op U))).surjective
      (G.obj.map f.op x)
  apply (Sheaf.isLocallyBijective_iff_isIso φ).mp
  exact ⟨hi, hs⟩

end Motivic.SmoothSite
