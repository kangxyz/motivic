/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Presentation.Local
public import Motivic.Cohomology.A1.LocalVanishing.OpenImage.Basic
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.OriginalEtalePresentation

/-! # Original affine local zero from the constructed simultaneous presentation

The only geometric input is the original affine smooth integral scheme, its nonzero
closed bad ideal and complementary affine open. Neither presentation nor frames,
sections, finite-flat divisors or correcting correspondences are supplied.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open AlgebraicGeometry.Scheme.RelativeCurve QuadraticIncidence.InfinityChart
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]
local instance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The original smooth affine scheme, with its original k-structure. -/
abbrev originalAffineObject : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (Spec.map (CommRingCat.ofHom (algebraMap k B)))

/-- Closed-point local vanishing for arbitrary HI presheaves with transfers over an
infinite field. All moving geometry is produced from the original data. -/
theorem exists_original_affine_zero_neighborhood
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    ∃ (O : (Spec (.of B)).Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk
          (X := SmoothSite.mk (O.ι ≫ (originalAffineObject k B).hom))
          (Y := originalAffineObject k B) O.ι rfl)) v = 0 := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsAffine (originalAffineObject k B).left := inferInstanceAs (IsAffine (Spec (.of B)))
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have H : IsPullback z (𝟙 _) (𝟙 _) z := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e⟩ := nonempty_originalEtalePresentation k B x J hJ g hg d hd
    (𝟙 _) a.left z (by simp only [Category.comp_id]; rfl) H ha hcover
  have : IsAffine e.target := e.target_affine
  have : IsOpenImmersion e.refinement := e.refinement_open
  have : IsLocallyNoetherian e.target :=
    LocallyOfFiniteType.isLocallyNoetherian e.refinement
  have : IsNoetherian e.target := {}
  obtain ⟨O, hO, hx, hz⟩ := e.exists_zero_on_target_open
    (X := originalAffineObject k B) (A := A) (𝟙 _) a z z x P hP v hv
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ e.refinement ≫ (originalAffineObject k B).hom)
  let f : S ⟶ originalAffineObject k B :=
    SmoothSite.homMk (O.ι ≫ e.refinement) (by simp only [Category.assoc]; rfl)
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ e.refinement))
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_, ?_⟩
  · exact ⟨⟨e.point, hx⟩, e.point_eq⟩
  · exact P.zero_on_open_image f v hz

end Motivic.PresheafWithTransfers
