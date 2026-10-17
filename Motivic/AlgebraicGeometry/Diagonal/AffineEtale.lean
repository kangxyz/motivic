/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.TensorProduct.EtaleDiagonal
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Regular stalk presentations of actual affine diagonals

The stalk map of the actual scheme diagonal of `Spec S → Spec R` is identified
with localization of tensor multiplication using the affine fiber-product
isomorphism. An étale polynomial coordinate chart then supplies a genuine
regular list generating its kernel, over any commutative base ring.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
open RingTheory.Sequence

universe u v

namespace Motivic.AffineDiagonal

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The actual self-product of the affine scheme over its affine base. -/
abbrev product : Scheme :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The actual scheme diagonal into the affine self-product. -/
abbrev diagonal : Spec (CommRingCat.of S) ⟶ product R S :=
  pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S)))

set_option backward.isDefEq.respectTransparency false in
/-- The actual diagonal stalk map is isomorphic to localized tensor multiplication. -/
def arrowStalkIso (p : PrimeSpectrum S) :
    Arrow.mk ((diagonal R S).stalkMap p) ≅
      Arrow.mk (CommRingCat.ofHom
        (RelativePolynomialTensor.localMultiplication R S p.asIdeal)) := by
  rw [show diagonal R S =
    Spec.map (CommRingCat.ofHom (RelativePolynomialTensor.multiplication R S)) ≫
      (pullbackSpecIso R S S).inv from diagonal_SpecMap R S]
  refine (Arrow.isoMk
    (g := Arrow.mk ((Spec.map (CommRingCat.ofHom
      (RelativePolynomialTensor.multiplication R S))).stalkMap p))
    (asIso ((pullbackSpecIso R S S).inv.stalkMap
      ((Spec.map (CommRingCat.ofHom
        (RelativePolynomialTensor.multiplication R S))) p)))
    (Iso.refl _) ?_) ≪≫
      Scheme.arrowStalkMapSpecIso
        (CommRingCat.ofHom (RelativePolynomialTensor.multiplication R S)) p
  simp only [Arrow.mk_hom, Iso.refl_hom, Category.comp_id, asIso_hom,
    Scheme.Hom.stalkMap_comp]

/-- The ambient ring equivalence from the actual product stalk to the tensor localization. -/
def stalkEquiv (p : PrimeSpectrum S) :
    (product R S).presheaf.stalk (diagonal R S p) ≃+*
      Localization.AtPrime (RelativePolynomialTensor.diagonalPrime R S p.asIdeal) :=
  (Arrow.leftFunc.mapIso (arrowStalkIso R S p)).commRingCatIsoToRingEquiv

/-- The corresponding equivalence on the stalk of the source affine scheme. -/
def sourceStalkEquiv (p : PrimeSpectrum S) :
    (Spec (CommRingCat.of S)).presheaf.stalk p ≃+* Localization.AtPrime p.asIdeal :=
  (Arrow.rightFunc.mapIso (arrowStalkIso R S p)).commRingCatIsoToRingEquiv

/-- The two concrete ring equivalences intertwine the actual stalk map and local multiplication. -/
theorem localMultiplication_stalkEquiv (p : PrimeSpectrum S)
    (x : (product R S).presheaf.stalk (diagonal R S p)) :
    RelativePolynomialTensor.localMultiplication R S p.asIdeal (stalkEquiv R S p x) =
      sourceStalkEquiv R S p ((diagonal R S).stalkMap p x) := by
  exact ConcreteCategory.congr_hom (arrowStalkIso R S p).hom.w x

/-- The actual diagonal kernel is the inverse image of the localized multiplication kernel. -/
theorem ker_stalkMap (p : PrimeSpectrum S) :
    RingHom.ker ((diagonal R S).stalkMap p).hom =
      (RingHom.ker (RelativePolynomialTensor.localMultiplication R S p.asIdeal)).comap
        (stalkEquiv R S p) := by
  ext x
  change ((diagonal R S).stalkMap p).hom x = 0 ↔
    RelativePolynomialTensor.localMultiplication R S p.asIdeal (stalkEquiv R S p x) = 0
  rw [localMultiplication_stalkEquiv]
  exact (sourceStalkEquiv R S p).map_eq_zero_iff.symm

end Motivic.AffineDiagonal

namespace Motivic.AffineDiagonal

variable (R : Type u) (σ : Type v) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]

/-- A polynomial coordinate difference in the actual ambient scheme stalk. -/
def stalkDifference (p : PrimeSpectrum S) (i : σ) :
    (product R S).presheaf.stalk (diagonal R S p) :=
  (stalkEquiv R S p).symm (RelativePolynomialTensor.localDifference R σ S p.asIdeal i)

omit [IsScalarTower R (MvPolynomial σ R) S] in
@[simp]
theorem stalkEquiv_stalkDifference (p : PrimeSpectrum S) (i : σ) :
    stalkEquiv R S p (stalkDifference R σ S p i) =
      algebraMap (S ⊗[R] S)
        (Localization.AtPrime (RelativePolynomialTensor.diagonalPrime R S p.asIdeal))
        (1 ⊗ₜ[R] algebraMap (MvPolynomial σ R) S (MvPolynomial.X i) -
          algebraMap (MvPolynomial σ R) S (MvPolynomial.X i) ⊗ₜ[R] 1) :=
  (stalkEquiv R S p).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Flat polynomial coordinates give a regular sequence in the actual product stalk. -/
theorem isRegular_stalkDifferences [Module.Flat (MvPolynomial σ R) S]
    (p : PrimeSpectrum S) (l : List σ) (hl : l.Nodup) :
    IsRegular ((product R S).presheaf.stalk (diagonal R S p))
      (l.map (stalkDifference R σ S p)) := by
  let e := (stalkEquiv R S p).symm
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm
    (e : Localization.AtPrime (RelativePolynomialTensor.diagonalPrime R S p.asIdeal) →+*
      (product R S).presheaf.stalk (diagonal R S p))
    (e.symm : (product R S).presheaf.stalk (diagonal R S p) →+*
      Localization.AtPrime (RelativePolynomialTensor.diagonalPrime R S p.asIdeal))
  have h := (e.toSemilinearEquiv.isRegular_congr'
    (l.map (RelativePolynomialTensor.localDifference R σ S p.asIdeal))).mp
      (RelativePolynomialTensor.isRegular_localDifferences R σ S p.asIdeal l hl)
  convert! h using 1
  simp only [List.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate differences generate the actual diagonal stalk kernel. -/
theorem ker_stalkMap_eq_ofList
    [Algebra.EssFiniteType (MvPolynomial σ R) S]
    [Algebra.FormallyUnramified (MvPolynomial σ R) S]
    (p : PrimeSpectrum S) (l : List σ) (hcover : ∀ i, i ∈ l) :
    RingHom.ker ((diagonal R S).stalkMap p).hom =
      Ideal.ofList (l.map (stalkDifference R σ S p)) := by
  rw [ker_stalkMap, RelativePolynomialTensor.ker_localMultiplication_eq_ofList
    R σ S p.asIdeal l hcover,
    ← Ideal.map_symm (stalkEquiv R S p)]
  change (Ideal.ofList (l.map
    (RelativePolynomialTensor.localDifference R σ S p.asIdeal))).map
      (stalkEquiv R S p).symm.toRingHom = _
  rw [Ideal.map_ofList]
  simp only [List.map_map]
  rfl

/-- Étale polynomial coordinates present the actual scheme diagonal stalk by a regular list. -/
theorem etale_stalkPresentation [Algebra.Etale (MvPolynomial σ R) S]
    (p : PrimeSpectrum S) (l : List σ) (hl : l.Nodup) (hcover : ∀ i, i ∈ l) :
    IsRegular ((product R S).presheaf.stalk (diagonal R S p))
      (l.map (stalkDifference R σ S p)) ∧
    RingHom.ker ((diagonal R S).stalkMap p).hom =
      Ideal.ofList (l.map (stalkDifference R σ S p)) :=
  ⟨isRegular_stalkDifferences R σ S p l hl,
    ker_stalkMap_eq_ofList R σ S p l hcover⟩

end Motivic.AffineDiagonal
