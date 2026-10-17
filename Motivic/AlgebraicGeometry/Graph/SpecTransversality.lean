/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Graph.CommonStalkTransport

/-!
# The same diagonal list on actual affine tensor-spectrum stalks

The explicit local diagonal list is transported to the stalks of the actual
tensor spectra. Its literal images under the actual graph pair map remain
regular. All point identifications are explicit, and the map on the graph
source is arbitrary.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open RingTheory.Sequence

universe u v

namespace Motivic.Graph

set_option backward.isDefEq.respectTransparency false in
/-- Stalk localization intertwines the actual aligned spectrum map with its local ring map. -/
theorem alignedStalkMap_spec_stalkIso {R S : CommRingCat.{u}}
    (f : R ⟶ S) (p : PrimeSpectrum S) (q : PrimeSpectrum R) (h : q = p.comap f.hom) :
    alignedStalkMap (Spec.map f) p q h ≫ (Spec.stalkIso S p).hom =
      (Spec.stalkIso R q).hom ≫ CommRingCat.ofHom
        (Localization.localRingHom q.asIdeal p.asIdeal f.hom
          (congrArg PrimeSpectrum.asIdeal h)) := by
  subst q
  exact (congrArg (fun k => k ≫ (Spec.stalkIso S p).hom)
    (alignedStalkMap_rfl (Spec.map f) p)).trans
      (Scheme.arrowStalkMapSpecIso f p).hom.w.symm

end Motivic.Graph

namespace Motivic.PolynomialTensorGraph

variable (R : Type u) (σ : Type v) (A B : Type u)
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra (MvPolynomial σ R) B] [IsScalarTower R (MvPolynomial σ R) B]
  (f : B →ₐ[MvPolynomial σ R] A)

/-- The actual point of the tensor spectrum on the graph. -/
def graphPoint (p : PrimeSpectrum A) : PrimeSpectrum (A ⊗[R] B) :=
  p.comap (evaluation R σ A B f).toRingHom

/-- The corresponding actual point of the target tensor square spectrum. -/
def diagonalPoint (p : PrimeSpectrum A) : PrimeSpectrum (B ⊗[R] B) :=
  (p.comap (f : B →+* A)).comap (RelativePolynomialTensor.multiplication R B)

/-- The actual pair map takes the graph tensor point to the diagonal tensor point. -/
theorem diagonalPoint_eq_comap_graphPoint (p : PrimeSpectrum A) :
    diagonalPoint R σ A B f p =
      (graphPoint R σ A B f p).comap (diagonalPullback R σ A B f).toRingHom := by
  apply PrimeSpectrum.ext
  exact (comap_graphPrime R σ A B f p.asIdeal).symm

set_option backward.isDefEq.respectTransparency false in
/-- One actual diagonal-stalk kernel list has regular images in the actual graph tensor stalk. -/
theorem spec_common_regular_list [Algebra.Etale (MvPolynomial σ R) B]
    (p : PrimeSpectrum A) (l : List σ) (hl : l.Nodup) (hcover : ∀ i, i ∈ l) :
    ∃ rs : List ((Spec (CommRingCat.of (B ⊗[R] B))).presheaf.stalk
      (diagonalPoint R σ A B f p)),
      IsRegular ((Spec (CommRingCat.of (B ⊗[R] B))).presheaf.stalk
        (diagonalPoint R σ A B f p)) rs ∧
      RingHom.ker ((Spec.map (CommRingCat.ofHom
        (RelativePolynomialTensor.multiplication R B))).stalkMap
          (p.comap (f : B →+* A))).hom = Ideal.ofList rs ∧
      IsRegular ((Spec (CommRingCat.of (A ⊗[R] B))).presheaf.stalk (graphPoint R σ A B f p))
        (rs.map (Graph.alignedStalkMap
          (Spec.map (CommRingCat.ofHom (diagonalPullback R σ A B f).toRingHom))
          (graphPoint R σ A B f p) (diagonalPoint R σ A B f p)
          (diagonalPoint_eq_comap_graphPoint R σ A B f p)).hom) := by
  apply Graph.exists_regular_kernel_and_regular_image_of_ringEquivs
    ((Spec.map (CommRingCat.ofHom (RelativePolynomialTensor.multiplication R B))).stalkMap
      (p.comap (f : B →+* A))).hom
    (Graph.alignedStalkMap
      (Spec.map (CommRingCat.ofHom (diagonalPullback R σ A B f).toRingHom))
      (graphPoint R σ A B f p) (diagonalPoint R σ A B f p)
      (diagonalPoint_eq_comap_graphPoint R σ A B f p)).hom
    (RelativePolynomialTensor.localMultiplication R B (p.comap (f : B →+* A)).asIdeal)
    (localDiagonalPullback R σ A B f p.asIdeal)
    (Spec.stalkIso (CommRingCat.of (B ⊗[R] B))
      (diagonalPoint R σ A B f p)).commRingCatIsoToRingEquiv
    (Spec.stalkIso (CommRingCat.of B) (p.comap (f : B →+* A))).commRingCatIsoToRingEquiv
    (Spec.stalkIso (CommRingCat.of (A ⊗[R] B))
      (graphPoint R σ A B f p)).commRingCatIsoToRingEquiv
  · intro r
    exact ConcreteCategory.congr_hom
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom
        (RelativePolynomialTensor.multiplication R B))
          (p.comap (f : B →+* A))).hom.w.symm r
  · intro r
    exact ConcreteCategory.congr_hom
      (Graph.alignedStalkMap_spec_stalkIso
        (CommRingCat.ofHom (diagonalPullback R σ A B f).toRingHom)
        (graphPoint R σ A B f p) (diagonalPoint R σ A B f p)
        (diagonalPoint_eq_comap_graphPoint R σ A B f p)) r
  · exact ⟨_, RelativePolynomialTensor.isRegular_localDifferences R σ B
      (p.comap (f : B →+* A)).asIdeal l hl,
      RelativePolynomialTensor.ker_localMultiplication_eq_ofList R σ B
        (p.comap (f : B →+* A)).asIdeal l hcover,
      isRegular_map_localDiagonalDifferences R σ A B f p.asIdeal l hl⟩

end Motivic.PolynomialTensorGraph
