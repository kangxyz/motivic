/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.OriginalAffineLocalVanishing
public import Motivic.Topology.JacobsonOpenCover
/-! Direct original-section moving and genuine missing-boundary audit. -/
set_option linter.hashCommand false
public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]
local instance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
example
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
  exact exists_original_affine_zero_neighborhood k B x J hJ g hg d hd a ha hcover P hP v hv
end Motivic.PresheafWithTransfers

#print axioms Motivic.PresheafWithTransfers.exists_original_affine_zero_neighborhood
#print axioms AlgebraicGeometry.Scheme.RelativeCurve.OriginalEtalePresentation.missing_finite
#print axioms TopologicalSpace.Opens.iSup_eq_top_of_closedPoint_neighborhoods
