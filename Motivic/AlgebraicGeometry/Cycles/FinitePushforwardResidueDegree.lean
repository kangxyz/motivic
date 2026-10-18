/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardStalk

/-!
# Actual residue degrees in the finite algebra fiber formula

The maximal quotient of the whole localized finite algebra is identified with
the residue field of the actual source scheme point, compatibly with the actual
target residue action. This compares the numerical algebraic and geometric
degrees without replacing the relevant scalar maps by abstract field isomorphisms.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteFiber

/-- Correcting the target point does not change the degree of the actual residue map. -/
theorem pointedSpecResidue_finrank {A B : CommRingCat.{u}} (f : A ⟶ B)
    (p : PrimeSpectrum A) (x : PrimeSpectrum B) (h : x.comap f.hom = p) :
    letI := (pointedSpecResidueMap f p x h).hom.toAlgebra
    Module.finrank ((Spec A).residueField p) ((Spec B).residueField x) =
      (Spec.map f).residueDegree x := by
  subst p
  rfl

attribute [local instance] Algebra.TensorProduct.rightAlgebra Ideal.Quotient.field

variable (A B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
  (p : PrimeSpectrum A) (q : MaximalSpectrum (localAlgebra A B p))

/-- The actual maximal quotient is finite over the target localization. -/
instance localAlgebraQuotient_finite :
    Module.Finite (Localization.AtPrime p.asIdeal) (localAlgebra A B p ⧸ q.asIdeal) := by
  have : Module.Finite (Localization.AtPrime p.asIdeal) (localAlgebra A B p) :=
    localAlgebra_finite A B p
  exact Module.Finite.trans (localAlgebra A B p) (localAlgebra A B p ⧸ q.asIdeal)

/-- The canonical residue action on the actual finite maximal quotient. -/
instance localAlgebraQuotientResidueAlgebra :
    Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
      (localAlgebra A B p ⧸ q.asIdeal) :=
  IsLocalRing.ResidueField.algebraOfIsIntegral (R := Localization.AtPrime p.asIdeal)
    (k := localAlgebra A B p ⧸ q.asIdeal)

/-- The maximal quotient and localized residue field have the same literal target residue action. -/
theorem quotientResidue_base_square :
    (Module.finiteAlgebraResidueQuotientEquiv (localAlgebra A B p) q).toRingHom.comp
        (algebraMap (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
          (localAlgebra A B p ⧸ q.asIdeal)) =
      IsLocalRing.ResidueField.map
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
  apply RingHom.ext
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  change Module.finiteAlgebraResidueQuotientEquiv (localAlgebra A B p) q
      (algebraMap (Localization.AtPrime p.asIdeal) (localAlgebra A B p ⧸ q.asIdeal) a) =
    IsLocalRing.residue _
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) a)
  rw [IsScalarTower.algebraMap_apply (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
    (localAlgebra A B p ⧸ q.asIdeal)]
  rw [(Module.finiteAlgebraResidueQuotientEquiv (localAlgebra A B p) q).commutes]
  rw [← IsScalarTower.algebraMap_apply (Localization.AtPrime p.asIdeal)
    (localAlgebra A B p) (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))]
  rfl

/-- The literal maximal quotient identifies with the actual source scheme residue field. -/
def sourceQuotientResidueIso :
    CommRingCat.of (localAlgebra A B p ⧸ q.asIdeal) ≅
      (Spec B).residueField (sourcePoint A B p q).1 :=
  (Module.finiteAlgebraResidueQuotientEquiv
    (localAlgebra A B p) q).toRingEquiv.toCommRingCatIso ≪≫
    sourceSchemeResidueIso A B p q

/-- The maximal-quotient comparison commutes with the actual target residue map. -/
theorem sourceQuotientResidueIso_base_square :
    (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
        (localAlgebra A B p ⧸ q.asIdeal)) :
      CommRingCat.of p.asIdeal.ResidueField ⟶
        CommRingCat.of (localAlgebra A B p ⧸ q.asIdeal)) ≫
      (sourceQuotientResidueIso A B p q).hom =
    (Scheme.Spec.residueFieldIso A p).inv ≫
      pointedSpecResidueMap (A := A) (B := B) (CommRingCat.ofHom (algebraMap A B)) p
        (sourcePoint A B p q).1 (sourcePoint A B p q).2 := by
  have hq : (CommRingCat.ofHom
      (algebraMap (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
        (localAlgebra A B p ⧸ q.asIdeal)) :
      CommRingCat.of p.asIdeal.ResidueField ⟶
        CommRingCat.of (localAlgebra A B p ⧸ q.asIdeal)) ≫
        (Module.finiteAlgebraResidueQuotientEquiv
          (localAlgebra A B p) q).toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (IsLocalRing.ResidueField.map
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) := by
    apply CommRingCat.hom_ext
    exact quotientResidue_base_square A B p q
  rw [sourceQuotientResidueIso, Iso.trans_hom, ← Category.assoc, hq,
    sourceSchemeResidueIso_base_square]

/-- The actual source residue field is finite over the actual pointed target residue field. -/
theorem sourceSchemeResidue_finite :
    letI := (pointedSpecResidueMap (A := A) (B := B)
      (CommRingCat.ofHom (algebraMap A B)) p
        (sourcePoint A B p q).1 (sourcePoint A B p q).2).hom.toAlgebra
    Module.Finite ((Spec A).residueField p) ((Spec B).residueField (sourcePoint A B p q).1) := by
  let := (pointedSpecResidueMap (A := A) (B := B)
    (CommRingCat.ofHom (algebraMap A B)) p
      (sourcePoint A B p q).1 (sourcePoint A B p q).2).hom.toAlgebra
  have : Module.Finite (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
      (localAlgebra A B p ⧸ q.asIdeal) :=
    Module.finiteAlgebra_residue_finite (Localization.AtPrime p.asIdeal) (localAlgebra A B p) q
  exact Module.Finite.of_equiv_equiv
    (Scheme.Spec.residueFieldIso A p).symm.commRingCatIsoToRingEquiv
    (sourceQuotientResidueIso A B p q).commRingCatIsoToRingEquiv
    (congrArg CommRingCat.Hom.hom (sourceQuotientResidueIso_base_square A B p q)).symm

/-- The finite-algebra weight is exactly the residue degree used by finite scheme pushforward. -/
theorem finiteAlgebraResidueDegree_eq_schemeResidueDegree :
    Module.finiteAlgebraResidueDegree (Localization.AtPrime p.asIdeal)
        (localAlgebra A B p) q =
      (Spec.map (CommRingCat.ofHom (algebraMap A B) : A ⟶ B)).residueDegree
        (sourcePoint A B p q).1 := by
  let := (pointedSpecResidueMap (A := A) (B := B)
    (CommRingCat.ofHom (algebraMap A B)) p
      (sourcePoint A B p q).1 (sourcePoint A B p q).2).hom.toAlgebra
  change Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))
    (localAlgebra A B p ⧸ q.asIdeal) = _
  calc
    _ = Module.finrank ((Spec A).residueField p)
        ((Spec B).residueField (sourcePoint A B p q).1) := by
      apply Algebra.finrank_eq_of_equiv_equiv
        (Scheme.Spec.residueFieldIso A p).symm.commRingCatIsoToRingEquiv
        (sourceQuotientResidueIso A B p q).commRingCatIsoToRingEquiv
      exact (congrArg CommRingCat.Hom.hom (sourceQuotientResidueIso_base_square A B p q)).symm
    _ = _ := pointedSpecResidue_finrank (A := A) (B := B)
      (CommRingCat.ofHom (algebraMap A B)) p
        (sourcePoint A B p q).1 (sourcePoint A B p q).2

end Motivic.FiniteFiber
