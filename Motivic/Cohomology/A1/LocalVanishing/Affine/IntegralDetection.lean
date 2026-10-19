/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.DenseOpen.AffineDetection
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates

/-! # Dense-open detection on an original integral affine smooth-site object -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open _root_.AlgebraicGeometry.Scheme.SmoothSite
variable {k : Type u} [Field k] [Infinite k]

/-- Canonical affine coordinates are only used internally: both the section and
returned affine neighborhood belong to the original smooth-site object. -/
theorem exists_zero_neighborhood_of_integral_affine
    {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsIntegral X.left]
    [Nonempty A.left] (a : A ⟶ X) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left) :
    ∃ (O : X.left.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  let : Algebra k Γ(X.left, ⊤) := AffineCoordinates.sectionsAlgebra X
  let e : originalAffineObject k Γ(X.left, ⊤) ≅ X := AffineCoordinates.affineIso X
  have : IsOpenImmersion (a ≫ e.inv).left :=
    inferInstanceAs (IsOpenImmersion (a.left ≫ X.left.isoSpec.hom))
  have hv' : P.transfer ((Cor.graphFunctor k).map (a ≫ e.inv))
      (P.transfer ((Cor.graphFunctor k).map e.hom) v) = 0 := by
    have he : (a ≫ e.inv) ≫ e.hom = a := by simp
    have hv' := hv
    rw [← he, Functor.map_comp, transfer_comp] at hv'
    exact hv'
  obtain ⟨O, hx, hO, hz⟩ := exists_zero_neighborhood_of_nonempty_open
    k Γ(X.left, ⊤) (a ≫ e.inv) P hP (P.transfer ((Cor.graphFunctor k).map e.hom) v)
      hv' (e.inv.left x)
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ (originalAffineObject k Γ(X.left, ⊤)).hom)
  let j : S ⟶ originalAffineObject k Γ(X.left, ⊤) := SmoothSite.homMk O.ι rfl
  let f := j ≫ e.hom
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left :=
    inferInstanceAs (IsOpenImmersion (O.ι ≫ X.left.isoSpec.inv))
  have hf : P.transfer ((Cor.graphFunctor k).map f) v = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hz
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_, P.zero_on_open_image f v hf⟩
  refine ⟨⟨e.inv.left x, hx⟩, ?_⟩
  change e.hom.left (e.inv.left x) = x
  have he := congrArg (fun f => f.left x) e.inv_hom_id
  exact he

end Motivic.PresheafWithTransfers
