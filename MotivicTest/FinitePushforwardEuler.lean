/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardEuler
public import Motivic.Algebra.Homology.KoszulHyperhomologyPlacement

/-!
# Original-complex finite pushforward consumers

The finite pushforward identity is used for arbitrary quotient maps and for
original complexes with a constructed scalar-one contraction. The latter has
no restriction on any original term's length, degree support, or homology.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex

universe u

namespace Motivic.MotivicTest.FinitePushforwardEuler

open FiniteFiber LengthEuler

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A : CommRingCat.{u}) (I : Ideal A) (p : PrimeSpectrum A)
  [IsNoetherianRing (Localization.AtPrime p.asIdeal)]

/-- Every finite quotient map, including nonradical and nonflat ones, has the
actual source-fiber formula for the original complex under its sole local homology premise. -/
theorem quotientProjection (K : ChainComplex (ModuleCat.{u} (A ⧸ I)) ℕ)
    (hK : FiniteHomology (wholeCoefficientComplex A (.of (A ⧸ I)) p K)) :
    chainEuler (actualPushforwardStalkComplex A (.of (A ⧸ I)) p K)
        (actualPushforwardStalk_finiteHomology A (.of (A ⧸ I)) p K hK) =
      ∑ᶠ x : {x : PrimeSpectrum (A ⧸ I) // x.comap (Ideal.Quotient.mk I) = p},
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).residueDegree x.1 : ℤ) *
          chainEuler (actualSourceStalkComplex (.of (A ⧸ I)) x.1 K)
            (actualFiberStalk_finiteHomology A (.of (A ⧸ I)) p K hK x) :=
  actualFinitePushforwardChainEuler A (.of (A ⧸ I)) p K hK

variable (B : CommRingCat.{u}) [Algebra A B] [Module.Finite A B]

omit [IsNoetherianRing (Localization.AtPrime p.asIdeal)] [Module.Finite A B] in
/-- Extension of the original scalar-one contraction constructs finite local
homology, even when the original coefficient complex is entirely unrestricted. -/
theorem contractibleWholeFinite (K : ChainComplex (ModuleCat.{u} B) ℕ) :
    FiniteHomology (wholeCoefficientComplex A B p
      (tensorObj (Koszul.singleComplex B 1) K)) := by
  apply Koszul.finiteHomology_of_identity_homotopy
  let F := ModuleCat.extendScalars (algebraMap B (localAlgebra A B p))
  exact (Homotopy.ofEq ((F.mapHomologicalComplex _).map_id _).symm).trans
    ((F.mapHomotopy (Koszul.singleUnitTensorHomotopy K)).trans
      (Homotopy.ofEq ((F.mapHomologicalComplex _).map_zero _ _)))

/-- The actual sheaf-stalk fiber formula consumes the constructed contraction,
without any externally assumed local or global length bounds on the original K. -/
theorem unrestrictedContractibleProjection (K : ChainComplex (ModuleCat.{u} B) ℕ) :
    chainEuler (actualPushforwardStalkComplex A B p (tensorObj (Koszul.singleComplex B 1) K))
        (actualPushforwardStalk_finiteHomology A B p _ (contractibleWholeFinite A p B K)) =
      ∑ᶠ x : {x : PrimeSpectrum B // x.comap (algebraMap A B) = p},
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueDegree x.1 : ℤ) *
          chainEuler (actualSourceStalkComplex B x.1 (tensorObj (Koszul.singleComplex B 1) K))
            (actualFiberStalk_finiteHomology A B p _ (contractibleWholeFinite A p B K) x) :=
  actualFinitePushforwardChainEuler A B p _ (contractibleWholeFinite A p B K)

omit [IsNoetherianRing (Localization.AtPrime p.asIdeal)] in
/-- The actual localized original differentials commute with the source-stalk comparison. -/
theorem localizedOriginalDifferentials (K : ChainComplex (ModuleCat.{u} B) ℕ)
    (q : MaximalSpectrum (localAlgebra A B p)) (i j : ℕ) :
    let C := ((localCoefficientFunctor A B p q).mapHomologicalComplex _).obj K
    let D := ((restrictedSourceStalkFunctor A B p q).mapHomologicalComplex _).obj K
    let e := (localCoefficientStalkComplexIso A B p q _).app K
    e.hom.f i ≫ D.d i j = C.d i j ≫ e.hom.f j :=
  ((localCoefficientStalkComplexIso A B p q _).app K).hom.comm i j

end Motivic.MotivicTest.FinitePushforwardEuler
