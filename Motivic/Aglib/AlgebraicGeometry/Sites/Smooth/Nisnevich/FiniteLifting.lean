/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteLifting
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
# Finite-support Nisnevich lifting in the smooth site

Over an affine base, actual residue-field lifts of a separated étale morphism
along one finite fiber give a lift of the entire support after a pointed
Nisnevich neighborhood in the smooth site. The scheme-level neighborhood is
restricted to an affine open around its distinguished point. Affineness gives
separatedness and quasi-compactness of its structure morphism; neither property
is assumed of the original étale neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Lift the whole finite support after an actual smooth-site Nisnevich
neighborhood. The fiber may be empty and the support may be nonreduced. -/
theorem exists_nisnevich_lift_of_isFinite
    {S : Scheme.{u}} [IsAffine S] (X : SmoothSite S)
    {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p] (x : X.left)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = x → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (U : SmoothSite S) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ b : pullback p g.left ⟶ V, b ≫ q = pullback.fst p g.left := by
  obtain ⟨W, h, hh, w, hw, hr, b, hb⟩ :=
    AlgebraicGeometry.exists_nisnevich_lift_of_isFinite p x q hq
  obtain ⟨u, hu⟩ := W.affineCover.covers w
  let j := W.affineCover.f (W.affineCover.idx w)
  let U : SmoothSite S := mk (j ≫ h ≫ X.hom)
  let g : U ⟶ X := homMk (j ≫ h) (by simp [U])
  let a : pullback p g.left ⟶ pullback p h :=
    pullback.map p g.left p h (𝟙 Z) j (𝟙 X.left) (by simp) (by simp [g])
  refine ⟨U, g, ?_, u, ?_, ?_, a ≫ b, ?_⟩
  · change Etale (j ≫ h)
    infer_instance
  · change h (j u) = x
    rw [hu, hw]
  · change IsIso ((j ≫ h).residueFieldMap u)
    rw [Scheme.residueFieldMap_comp]
    have : IsIso (h.residueFieldMap (j u)) := by rw [hu]; exact hr
    infer_instance
  · rw [Category.assoc, hb]
    simp [a]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite family of pointed smooth-site Nisnevich neighborhoods has a common
pointed refinement in the same smooth site, with actual maps to every member.
The empty family is allowed. -/
theorem exists_common_nisnevich_refinement
    {S : Scheme.{u}} [IsAffine S] (X : SmoothSite S) (x : X.left) (n : ℕ)
    (U : Fin n → SmoothSite S) (g : ∀ i, U i ⟶ X)
    (hg : ∀ i, Etale (g i).left) (u : ∀ i, (U i).left)
    (hu : ∀ i, (g i).left (u i) = x)
    (hr : ∀ i, IsIso ((g i).left.residueFieldMap (u i))) :
    ∃ (W : SmoothSite S) (h : W ⟶ X), Etale h.left ∧
    ∃ w : W.left, h.left w = x ∧ IsIso (h.left.residueFieldMap w) ∧
    ∃ a : ∀ i, W ⟶ U i, (∀ i, a i ≫ g i = h) ∧
      (∀ i, (a i).left w = u i) := by
  obtain ⟨W, h, hh, w, hw, hwr, a, ha, haw⟩ :=
    AlgebraicGeometry.exists_common_nisnevich_refinement x n
      (fun i ↦ (U i).left) (fun i ↦ (g i).left) hg u hu hr
  obtain ⟨w', hw'⟩ := W.affineCover.covers w
  let j := W.affineCover.f (W.affineCover.idx w)
  let W' : SmoothSite S := mk (j ≫ h ≫ X.hom)
  let h' : W' ⟶ X := homMk (j ≫ h) (by simp [W'])
  let a' (i : Fin n) : W' ⟶ U i := homMk (j ≫ a i) (by
    change (j ≫ a i) ≫ (U i).hom = j ≫ h ≫ X.hom
    rw [← MorphismProperty.Over.w (g i), Category.assoc,
      ← Category.assoc (a i), ha])
  refine ⟨W', h', ?_, w', ?_, ?_, a', ?_, ?_⟩
  · change Etale (j ≫ h)
    infer_instance
  · change h (j w') = x
    rw [hw', hw]
  · change IsIso ((j ≫ h).residueFieldMap w')
    rw [Scheme.residueFieldMap_comp]
    have : IsIso (h.residueFieldMap (j w')) := by rw [hw']; exact hwr
    infer_instance
  · intro i
    apply MorphismProperty.Over.Hom.ext
    change (j ≫ a i) ≫ (g i).left = j ≫ h
    rw [Category.assoc, ha]
  · intro i
    change a i (j w') = u i
    rw [hw', haw]

end AlgebraicGeometry.Scheme.SmoothSite
