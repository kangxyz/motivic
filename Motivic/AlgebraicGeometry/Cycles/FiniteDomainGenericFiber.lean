/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardResidueDegree
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The whole generic fiber of an injective finite map of domains

This leaf first proves injectivity, nontriviality and the domain
property for the actual tensor localization. Only then does finiteness over the
generic target field imply that the whole algebra is a field. Its zero maximal
point contracts to the source zero prime. The whole-algebra residue comparison
is induced by the zero quotient and the existing actual scheme residue map.
No exterior base change, reduced exterior ring or single exterior branch is asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteDomainGenericFiber

open FiniteFiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra Ideal.Quotient.field

/-- The generic prime of a domain, literally its zero ideal. -/
def zeroPrime (A : Type u) [CommRing A] [IsDomain A] : PrimeSpectrum A :=
  ⟨⊥, inferInstance⟩

variable (A B : CommRingCat.{u}) [IsDomain A] [IsDomain B] [Algebra A B]

/-- The base localization is the actual fraction ring, with its original A-action. -/
theorem genericLocal_isFractionRing :
    IsFractionRing A (Localization.AtPrime (zeroPrime A).asIdeal) := by
  change IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A))
  rw [← Ideal.primeCompl_bot]
  infer_instance

/-- The image denominators remain nonzero in B by the given injective map. -/
theorem denominators_le_nonZeroDivisors (hAB : Function.Injective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B (zeroPrime A).asIdeal.primeCompl ≤
      nonZeroDivisors B := by
  apply map_le_nonZeroDivisors_of_injective (algebraMap A B) hAB
  exact (zeroPrime A).asIdeal.primeCompl_le_nonZeroDivisors

/-- The literal B-map into the whole tensor localization is injective. -/
theorem sourceMap_injective (hAB : Function.Injective (algebraMap A B)) :
    Function.Injective (algebraMap B (localAlgebra A B (zeroPrime A))) :=
  IsLocalization.injective _ (denominators_le_nonZeroDivisors A B hAB)

/-- Nontriviality is established before constructing any field structure. -/
theorem whole_nontrivial (hAB : Function.Injective (algebraMap A B)) :
    Nontrivial (localAlgebra A B (zeroPrime A)) :=
  (sourceMap_injective A B hAB).nontrivial

/-- The whole tensor localization is a domain, before any maximal quotient is taken. -/
theorem whole_isDomain (hAB : Function.Injective (algebraMap A B)) :
    IsDomain (localAlgebra A B (zeroPrime A)) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (denominators_le_nonZeroDivisors A B hAB)

/-- The actual source zero prime contracts to the actual target zero prime. -/
theorem zeroPrime_comap (hAB : Function.Injective (algebraMap A B)) :
    (zeroPrime B).comap (algebraMap A B) = zeroPrime A := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective (algebraMap A B) hAB

variable [Module.Finite A B]

/-- Finiteness over the generic target field makes the whole domain a field. -/
theorem whole_isField (hAB : Function.Injective (algebraMap A B)) :
    IsField (localAlgebra A B (zeroPrime A)) := by
  let := genericLocal_isFractionRing A
  let : Field (Localization.AtPrime (zeroPrime A).asIdeal) := IsFractionRing.toField A
  let := whole_isDomain A B hAB
  let := localAlgebra_finite A B (zeroPrime A)
  let := IsArtinianRing.of_finite (Localization.AtPrime (zeroPrime A).asIdeal)
    (localAlgebra A B (zeroPrime A))
  exact IsArtinianRing.isField_of_isDomain _

/-- Only after the whole-algebra field proof do we select its zero maximal ideal. -/
def zeroMaximal (hAB : Function.Injective (algebraMap A B)) :
    MaximalSpectrum (localAlgebra A B (zeroPrime A)) := by
  let := (whole_isField A B hAB).toField
  exact ⟨⊥, Ideal.bot_isMaximal⟩

@[simp] theorem zeroMaximal_asIdeal (hAB : Function.Injective (algebraMap A B)) :
    (zeroMaximal A B hAB).asIdeal = ⊥ := rfl

/-- The actual localization contraction, rather than an assumed fiber label, is zero. -/
theorem sourcePoint_zero (hAB : Function.Injective (algebraMap A B)) :
    (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).1 = zeroPrime B := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective
    (algebraMap B (localAlgebra A B (zeroPrime A))) (sourceMap_injective A B hAB)

/-- Equal source points transport the actual pointed residue map. -/
theorem pointedResidueMap_congr_source {D E : CommRingCat.{u}} (f : D ⟶ E)
    (p : PrimeSpectrum D) (x y : PrimeSpectrum E)
    (hx : x.comap f.hom = p) (hy : y.comap f.hom = p) (hxy : x = y) :
    pointedSpecResidueMap f p x hx ≫ ((Spec E).residueFieldCongr hxy).hom =
      pointedSpecResidueMap f p y hy := by
  subst y
  simp

/-- The whole algebra maps to the residue field of its proved source point. -/
def wholeSourceResidueIso (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.of (localAlgebra A B (zeroPrime A)) ≅
      (Spec B).residueField
        (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).1 :=
  (RingEquiv.quotientBot (localAlgebra A B (zeroPrime A))).symm.toCommRingCatIso ≪≫
    sourceQuotientResidueIso A B (zeroPrime A) (zeroMaximal A B hAB)

/-- The whole algebra, not merely a branch quotient, is the actual generic source residue field. -/
def wholeResidueIso (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.of (localAlgebra A B (zeroPrime A)) ≅
      (Spec B).residueField (zeroPrime B) :=
  wholeSourceResidueIso A B hAB ≪≫
    (Spec B).residueFieldCongr (sourcePoint_zero A B hAB)

/-- The actual generic-local scalar square before transporting the source point. -/
theorem wholeSourceResidueIso_base_square (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.ofHom (algebraMap (Localization.AtPrime (zeroPrime A).asIdeal)
      (localAlgebra A B (zeroPrime A))) ≫ (wholeSourceResidueIso A B hAB).hom =
    (Spec.stalkIso A (zeroPrime A)).inv ≫ (Spec A).residue (zeroPrime A) ≫
      pointedSpecResidueMap (CommRingCat.ofHom (algebraMap A B)) (zeroPrime A)
        (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).1
        (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).2 := by
  let p := zeroPrime A
  let q := zeroMaximal A B hAB
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact ConcreteCategory.congr_hom
    (sourceQuotientResidueIso_base_square A B p q)
    (IsLocalRing.residue (Localization.AtPrime p.asIdeal) a)

/-- The K₀-square retains the original target stalk inverse, residue and residue-field map. -/
@[reassoc] theorem wholeResidueIso_base_square
    (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.ofHom (algebraMap (Localization.AtPrime (zeroPrime A).asIdeal)
      (localAlgebra A B (zeroPrime A))) ≫ (wholeResidueIso A B hAB).hom =
    (Spec.stalkIso A (zeroPrime A)).inv ≫ (Spec A).residue (zeroPrime A) ≫
      pointedSpecResidueMap (CommRingCat.ofHom (algebraMap A B)) (zeroPrime A)
        (zeroPrime B) (zeroPrime_comap A B hAB) := by
  rw [wholeResidueIso, Iso.trans_hom, ← Category.assoc,
    wholeSourceResidueIso_base_square]
  simp only [Category.assoc]
  rw [pointedResidueMap_congr_source]

/-- Reduction through the whole comparison retains the original B-localization map. -/
theorem wholeSourceResidueIso_source_square
    (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.ofHom (algebraMap B (localAlgebra A B (zeroPrime A))) ≫
        (wholeSourceResidueIso A B hAB).hom =
      (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤
        (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).1 trivial ≫
      (Spec B).residue
        (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).1 := by
  let p := zeroPrime A
  let q := zeroMaximal A B hAB
  rw [← Spec.algebraMap_stalkIso_inv_assoc]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  change (sourceSchemeResidueIso A B p q).hom
      (Module.finiteAlgebraResidueQuotientEquiv (localAlgebra A B p) q
        (algebraMap (localAlgebra A B p) (localAlgebra A B p ⧸ q.asIdeal)
          (algebraMap B (localAlgebra A B p) b))) = _
  rw [(Module.finiteAlgebraResidueQuotientEquiv (localAlgebra A B p) q).commutes]
  change (Spec B).residue (sourcePoint A B p q).1
      ((Spec.stalkIso B (sourcePoint A B p q).1).inv
        (sourceLocalizationEquiv A B p q
          (algebraMap B (Localization.AtPrime q.asIdeal) b))) = _
  rw [sourceLocalizationEquiv_algebraMap]
  rfl

/-- Equal-point transport preserves the original affine germ and residue. -/
theorem germ_residue_congr (D : CommRingCat.{u}) (x y : PrimeSpectrum D) (hxy : x = y) :
    (Scheme.ΓSpecIso D).inv ≫ (Spec D).presheaf.germ ⊤ x trivial ≫
        (Spec D).residue x ≫ ((Spec D).residueFieldCongr hxy).hom =
      (Scheme.ΓSpecIso D).inv ≫ (Spec D).presheaf.germ ⊤ y trivial ≫
        (Spec D).residue y := by
  subst y
  simp

/-- The B-square uses its original germ and residue, after proved equal-point transport. -/
@[reassoc] theorem wholeResidueIso_source_square
    (hAB : Function.Injective (algebraMap A B)) :
    CommRingCat.ofHom (algebraMap B (localAlgebra A B (zeroPrime A))) ≫
        (wholeResidueIso A B hAB).hom =
      (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ (zeroPrime B) trivial ≫
        (Spec B).residue (zeroPrime B) := by
  rw [wholeResidueIso, Iso.trans_hom, ← Category.assoc,
    wholeSourceResidueIso_source_square]
  simpa only [Category.assoc] using germ_residue_congr B
    (sourcePoint A B (zeroPrime A) (zeroMaximal A B hAB)).1 (zeroPrime B)
    (sourcePoint_zero A B hAB)

end Motivic.FiniteDomainGenericFiber
