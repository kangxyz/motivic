/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresentationLocalVanishing
public import Motivic.Cohomology.A1.GeneralOpenImageVanishing
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-! # Actual presentations give original Zariski zero neighborhoods

Only the post-presentation argument is used. It works over every field and
for an arbitrary coefficient universe. The presentation remains an explicit
geometric input; this does not assert finite-field existence of presentations.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic

universe u w

namespace AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation

/-- An actual presentation yields a literal affine open of the original target
containing its marked point, without any sheaf separatedness or field-size premise. -/
theorem exists_zero_on_original_open
    {k : Type u} [Field k] {X A : SmoothSite (Spec (.of k))}
    [IsAffine X.left] [IsAffine A.left] {Y Z : Scheme.{u}}
    (p : Y ⟶ X.left) (a : A ⟶ X) [IsOpenImmersion a.left]
    (z : Z ⟶ X.left) [IsClosedImmersion z] (s : Z ⟶ Y) (x : X.left)
    (e : OriginalEtalePresentation k X.hom p a.left z s x)
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have : IsAffine e.target := e.target_affine
  have : IsOpenImmersion e.refinement := e.refinement_open
  have : IsLocallyNoetherian e.target :=
    LocallyOfFiniteType.isLocallyNoetherian e.refinement
  have : IsNoetherian e.target := {}
  obtain ⟨O, hO, hx, hz⟩ := e.exists_zero_on_target_open p a z s x P hP v hv
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ e.refinement ≫ X.hom)
  let f : S ⟶ X := SmoothSite.homMk (O.ι ≫ e.refinement)
    (by simp only [Category.assoc]; rfl)
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ e.refinement))
  exact ⟨f.left.opensRange, isAffineOpen_opensRange f.left,
    ⟨⟨e.point, hx⟩, e.point_eq⟩, P.zero_on_open_image_general f v hz⟩

/-- A native scalar comparison is used only on sections and the resulting open
image; the presentation itself need not be transported field by field. -/
theorem exists_zero_on_original_open_of_iso
    {k : Type u} [Field k] {X₀ X A : SmoothSite (Spec (.of k))}
    [IsAffine X.left] [IsAffine A.left] {Y Z : Scheme.{u}}
    (i : X₀ ≅ X) (p : Y ⟶ X.left) (a : A ⟶ X) [IsOpenImmersion a.left]
    (z : Z ⟶ X.left) [IsClosedImmersion z] (s : Z ⟶ Y) (x : X₀.left)
    (e : OriginalEtalePresentation k X.hom p a.left z s (i.hom.left x))
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X₀))
    (hv : P.transfer ((Cor.graphFunctor k).map a)
      (P.transfer ((Cor.graphFunctor k).map i.inv) v) = 0) :
    ∃ O : X₀.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X₀.hom)) (Y := X₀) O.ι rfl)) v = 0 := by
  obtain ⟨O, hO, hx, hz⟩ := e.exists_zero_on_original_open p a z s _ P hP
    (P.transfer ((Cor.graphFunctor k).map i.inv) v) hv
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ X.hom)
  let j : S ⟶ X := SmoothSite.homMk O.ι rfl
  let f := j ≫ i.inv
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ i.inv.left))
  have hf : P.transfer ((Cor.graphFunctor k).map f) v = 0 := by
    rw [Functor.map_comp, PresheafWithTransfers.transfer_comp]
    exact hz
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_,
    P.zero_on_open_image_general f v hf⟩
  refine ⟨⟨i.hom.left x, hx⟩, ?_⟩
  exact congrArg (fun f => f.left x) i.hom_inv_id

end AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation
