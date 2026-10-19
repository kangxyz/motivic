/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormPrincipalCoefficient
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Original source-stalk principal quotients in the norm coefficient

The whole finite-algebra coefficient is transported to the actual source stalk
using its original source scalar map. Neither the source stalk nor its principal
quotient is assumed finite over the target stalk. This is the quotient transport
step toward signed principal-order compatibility, not yet global cycle pushforward.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormStalkLength`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineNormOrder`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u
namespace PrimeSpectrum.FiniteFiber

private theorem length_quotient_span_ringEquiv
    {R T : Type u} [CommRing R] [CommRing T] (e : R ≃+* T) (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) =
      Module.length T (T ⧸ Ideal.span {e a}) := by
  let I : Ideal R := Ideal.span {a}
  let J : Ideal T := Ideal.span {e a}
  let E : R ⧸ I ≃+* T ⧸ J := Ideal.quotientEquiv I J e (by
    simp [I, J, Ideal.map_span])
  let σ : R →+* T := e.toRingHom
  let : RingHomSurjective σ := ⟨e.surjective⟩
  let l : (R ⧸ I) →ₛₗ[σ] (T ⧸ J) :=
    { E.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
        change E (Ideal.Quotient.mk I (r * x)) =
          Ideal.Quotient.mk J (e r * e x)
        simp [E] }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective l E.bijective)]

/-- Localization of the actual principal quotient is the quotient by the
localized original equation, with no radical or support replacement. -/
theorem localizedPrincipalQuotientLength_eq_quotient
    {S : Type u} [CommRing S] (a : S) (q : MaximalSpectrum S) :
    _root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength a q =
      Module.length (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal ⧸
          Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a}) := by
  let L := Localization.AtPrime q.asIdeal
  let E := Algebra.TensorProduct.rid S L L
  let e₁ := Algebra.TensorProduct.tensorQuotientEquiv (R := S) L S L (Ideal.span {a})
  let e₂ := Ideal.quotientEquivAlg
    ((Ideal.span {a}).map (Algebra.TensorProduct.includeRight (R := S) (A := L)))
    (Ideal.span {algebraMap S L a}) E (by
      simp [E, Ideal.map_span, Algebra.TensorProduct.rid_tmul,
        Algebra.smul_def])
  exact (e₁.trans e₂).toLinearEquiv.length_eq

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
  (p : PrimeSpectrum A) (q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The source-stalk comparison sends the original source element to its
literal affine scheme germ, through the unchanged global-section map. -/
theorem sourceSchemeStalkIso_original_germ (a : B) :
    (_root_.AlgebraicGeometry.Scheme.Hom.FiniteFiber.sourceSchemeStalkIso A B p q).hom
        (algebraMap (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) (Localization.AtPrime
            q.asIdeal)
          (algebraMap B (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a)) =
      (Spec B).presheaf.germ ⊤ (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 trivial
        ((Scheme.ΓSpecIso B).inv a) := by
  rw [← IsScalarTower.algebraMap_apply]
  change (Spec.stalkIso B (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1).inv
      (_root_.PrimeSpectrum.FiniteFiber.sourceLocalizationEquiv A B p q
        (algebraMap B (Localization.AtPrime q.asIdeal) a)) = _
  rw [_root_.PrimeSpectrum.FiniteFiber.sourceLocalizationEquiv_algebraMap]
  exact ConcreteCategory.congr_hom
    (Spec.algebraMap_stalkIso_inv (R := B) (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1)
        a

/-- Every summand of the norm coefficient is the length of the original
source stalk modulo the original equation, not an abstractly chosen local ring. -/
theorem localizedPrincipalQuotientLength_eq_source_stalk (a : B) :
    _root_.PrimeSpectrum.FiniteFiber.localizedPrincipalQuotientLength (algebraMap B
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra A B p) a) q =
      Module.length ((Spec B).presheaf.stalk (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p
          q).1)
        (((Spec B).presheaf.stalk (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1) ⧸
          Ideal.span {(Spec B).presheaf.germ ⊤ (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p
              q).1 trivial
            ((Scheme.ΓSpecIso B).inv a)}) := by
  rw [localizedPrincipalQuotientLength_eq_quotient,
    length_quotient_span_ringEquiv
        (_root_.AlgebraicGeometry.Scheme.Hom.FiniteFiber.sourceSchemeStalkIso A B p
        q).commRingCatIsoToRingEquiv]
  exact congrArg
    (fun x : (Spec B).presheaf.stalk (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1 =>
      Module.length ((Spec B).presheaf.stalk (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p
          q).1)
        (((Spec B).presheaf.stalk (_root_.PrimeSpectrum.FiniteFiber.sourcePoint A B p q).1) ⧸
            Ideal.span {x}))
    (sourceSchemeStalkIso_original_germ A B p q a)

end PrimeSpectrum.FiniteFiber
