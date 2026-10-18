/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteCartierCylinderComparison
public import Motivic.AlgebraicGeometry.SmoothSiteCartierPunctureComparison
public import Motivic.Cohomology.A1.PresheafBoundaryEtaleExcision
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleMarkedPointDetection
public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointInverseImageComposition

/-! # Zero of the actual boundary on a smooth Cartier divisor

Actual local common étale charts compare the original pair with its own
zero-section cylinder. Conservativity uses every marked point of every small
test object, retaining the entire marking field. No global untwisted purity
isomorphism or assumed chart family occurs.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible

universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k]
  (P : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- Vanishing on literal zero-section cylinders implies vanishing on the
genuine closed inverse image for every actual smooth Cartier pair. -/
theorem isZero_presheafBoundary_of_smooth_cartier
    (hzero : ∀ D : SmoothSite (Spec (.of k)), IsZero (presheafBoundary P
      (SmoothSite.contractionOpen (.of k) D) (SmoothSite.a1Section (.of k) D 0)))
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    IsZero ((inverseImage i).obj (presheafBoundaryAmbient P j)) := by
  classical
  let G := presheafBoundaryAmbient P j
  let H := (inverseImage i).obj G
  have hlocal : ∀ z : Z, ∃ O : Z.Opens, z ∈ O ∧
      IsZero ((inverseImage O.ι).obj H) := by
    intro z
    obtain ⟨O, hz, V, a, b, d, ha, hb, hpa, hpb⟩ :=
      SmoothSite.exists_cartier_cylinder_comparison Y i hI z
    let : Etale a.left := ha
    let : Etale b.left := hb
    let D := SmoothSite.closedOpenSite (Y := Y) i O
    let c := SmoothSite.contractionOpen (.of k) D
    let q := SmoothSite.etalePullbackFst j a
    let w := SmoothSite.etalePullbackSnd j a
    obtain ⟨hA, t, hB⟩ :=
      SmoothSite.exists_cartier_puncture_comparison (.of k) j a b d i O.ι hpa hpb hcomp
    have hd : d ≫ b = SmoothSite.a1Section (.of k) D 0 := by
      apply MorphismProperty.Over.Hom.ext
      change d.left ≫ b.left = (SmoothSite.a1Section (.of k) D 0).left
      simpa only [Category.id_comp] using hpb.w
    have hBzero : IsZero (presheafBoundary P c (d ≫ b)) := by
      rw [hd]
      exact hzero D
    have hWzero : IsZero (presheafBoundary P w d) :=
      hBzero.of_iso (presheafBoundaryEtaleExcisionIso P c b w t hB d).symm
    have hDzero := isZero_presheafBoundary_of_etale P j a w q hA d hWzero
    change IsZero ((inverseImage (d.left ≫ a.left)).obj G) at hDzero
    rw [hpa.w] at hDzero
    exact ⟨O, hz, hDzero.of_iso ((inverseImageCompIso O.ι i).app G)⟩
  apply isZero_of_all_marked_residue_fibers H
  intro V z
  let K := V.left.residueField z
  let b : Spec K ⟶ Z := V.left.fromSpecResidueField z ≫ V.hom
  let p : Spec K := IsLocalRing.closedPoint K
  obtain ⟨O, hO, hH⟩ := hlocal (b p)
  exact fieldPoint_isZero_of_inverseImage_of_mem_range O.ι K H b p
    ⟨⟨b p, hO⟩, rfl⟩ hH

end Motivic.FiniteEtaleSite
