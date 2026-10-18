/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteAffineCoordinates
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Closed points in the actual affine zero coordinates

Closedness is transported through the canonical affine isomorphism and the
literal surjective evaluation homomorphism. No residue field is identified with
the ground field, and no rational point is introduced.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.SmoothSiteAffineCoordinates

variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

/-- The literal zero image of an original closed affine point has a maximal ideal. -/
theorem affineZeroPoint_isMaximal (X : SmoothSite (Spec (.of k))) [IsAffine X.left]
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    (show PrimeSpectrum (Polynomial Γ(X.left, ⊤)) from
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X.left, ⊤))))
        ((affineIso X).inv.left x)).asIdeal.IsMaximal := by
  have hc : IsClosed ({(affineIso X).inv.left x} : Set (Spec Γ(X.left, ⊤))) := by
    rw [affineIso_inv_left]
    have hc := X.left.isoSpec.hom.isClosedEmbedding.isClosedMap ({x} : Set X.left) hx
    rw [Set.image_singleton] at hc
    exact hc
  have hm : (show PrimeSpectrum Γ(X.left, ⊤) from
      (affineIso X).inv.left x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hc
  let := hm
  exact Ideal.comap_isMaximal_of_surjective
    (Polynomial.evalRingHom (0 : Γ(X.left, ⊤)))
    (fun r => ⟨Polynomial.C r, Polynomial.eval_C⟩)

end Motivic.SmoothSiteAffineCoordinates
