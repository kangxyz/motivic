/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardRelative

/-!
# Original finite-map Koszul projection from relative quasi-coherence

The whole finite algebra, original source fiber, target list, stalk maps and
residue weights are exactly those of the accepted global comparison. Only
quasi-coherence on the full inverse image of the chosen target affine open is
needed. The genuine whole-total finite-homology premise remains separate.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.RelativeFiniteSchemeEuler

open FiniteAffineChart LengthEuler FiniteSchemeEuler

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The whole coefficient algebra uses the literal original section map. -/
local instance koszulCoordinateAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K : ChainComplex X.Modules ℕ)
  [∀ n, ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj (K.X n)).IsQuasicoherent]

/-- The original global pushforward complex is the whole finite coefficient
complex restricted through the actual target stalk-localization equivalence. -/
def originalWholePushforwardIso :
    finiteAlgebraRestrictedComplex (Localization.AtPrime p.asIdeal)
        (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
        (originalWholeLocalizedComplex f hU p K) ≅
      (Functor.mapHomologicalComplex
        (ModuleCat.restrictScalars (targetStalkLocalizationIso hU p).inv.hom) _).obj
        (originalPushforwardStalkComplex f hU p K) := by
  have := coordinateFinite f hU
  exact (FiniteFiber.primePushforwardComplexIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
      (originalCoordinateComplex f hU K)).symm ≪≫
    ((ModuleCat.restrictScalars (Spec.stalkIso Γ(Y, U) p).inv.hom).mapHomologicalComplex _).mapIso
        (RelativeAffineQuasicoherent.wholeChartPushforwardStalkIso f hU _ K p) ≪≫
    (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsComp
      (Spec.stalkIso Γ(Y, U) p).inv.hom (inv (hU.fromSpec.stalkMap p)).hom).symm _).app
        (originalPushforwardStalkComplex f hU p K)

variable (q : MaximalSpectrum (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p))

/-- Use the commutative-localization ring structure in all categorical endpoints. -/
local instance canonicalKoszulLocalizationRing : Ring (Localization.AtPrime q.asIdeal) :=
  (inferInstance : CommRing (Localization.AtPrime q.asIdeal)).toRing

/-- The original source complex is the actual localization of the whole
coefficient complex, with the original structure-stalk action. -/
def originalWholeSourceIso :
    finiteAlgebraLocalizedComplex (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
        (originalWholeLocalizedComplex f hU p K) q ≅
      (Functor.mapHomologicalComplex
        (ModuleCat.restrictScalars (originalSourceLocalizationIso f hU p q).hom.hom) _).obj
        (originalSourceStalkComplex K
          (sourceChart f hU (wholeAlgebraSourcePoint f hU p q).1)) := by
  have := coordinateFinite f hU
  exact (FiniteFiber.localCoefficientStalkComplexIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p q _).app
      (originalCoordinateComplex f hU K) ≪≫
    (Functor.mapHomologicalComplex (ModuleCat.restrictScalars
        (FiniteFiber.sourceSchemeStalkIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p q).hom.hom) _).mapIso
        (RelativeAffineQuasicoherent.wholeChartStalkIso f hU _ K
          (wholeAlgebraSourcePoint f hU p q).1) ≪≫
    (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsComp
      (FiniteFiber.sourceSchemeStalkIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p q).hom.hom
      (inv ((sourceChart f hU).stalkMap
        (wholeAlgebraSourcePoint f hU p q).1)).hom).symm _).app
        (originalSourceStalkComplex K
          (sourceChart f hU (wholeAlgebraSourcePoint f hU p q).1))

private def koszulRestrictComparison {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) (s : List R) {C : ChainComplex (ModuleCat.{u} R) ℕ}
    {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (e : C ≅ ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj D) :
    HomologicalComplex.tensorObj (Koszul.chainComplex s) C ≅
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj
        (HomologicalComplex.tensorObj (Koszul.chainComplex (s.map φ)) D) :=
  (Koszul.koszulTensorFunctor s).mapIso e ≪≫ (Koszul.koszulTensorRestrictIso φ s D).symm

private theorem koszulTransportLength {R T : Type u} [CommRing R] [CommRing T]
    (φ : R ≃+* T) (s : List R) {C : ChainComplex (ModuleCat.{u} R) ℕ}
    {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (e : C ≅ ((ModuleCat.restrictScalars φ.toRingHom).mapHomologicalComplex _).obj D) (n : ℕ) :
    Module.length R ((HomologicalComplex.tensorObj (Koszul.chainComplex s) C).homology n) =
      Module.length T
        ((HomologicalComplex.tensorObj
          (Koszul.chainComplex (s.map φ.toRingHom)) D).homology n) := by
  let E := HomologicalComplex.tensorObj (Koszul.chainComplex (s.map φ.toRingHom)) D
  have h := ((E.sc n).mapHomologyIso
    (ModuleCat.restrictScalars φ.toRingHom)).toLinearEquiv.length_eq
  exact ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (koszulRestrictComparison φ.toRingHom s e)).toLinearEquiv.length_eq.trans
    (h.trans (TorComparison.length_restrictScalars_of_surjective φ.toRingHom φ.surjective _))

/-- The actual base-ring Koszul tensor has exactly the original global pushforward-stalk lengths. -/
theorem originalPushforwardKoszul_homology_length
    (s : List (Y.presheaf.stalk (hU.fromSpec p))) (n : ℕ) :
    Module.length (Localization.AtPrime p.asIdeal)
      ((Koszul.finiteProjectionSource (Localization.AtPrime p.asIdeal)
        (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
        (s.map (targetStalkLocalizationIso hU p).hom.hom)
        (originalWholeLocalizedComplex f hU p K)).homology n) =
      Module.length (Y.presheaf.stalk (hU.fromSpec p))
        ((originalPushforwardKoszul f hU p K s).homology n) := by
  have h := koszulTransportLength
    (targetStalkLocalizationIso hU p).symm.commRingCatIsoToRingEquiv
    (s.map (targetStalkLocalizationIso hU p).hom.hom) (originalWholePushforwardIso f hU p K) n
  have hl : (s.map (targetStalkLocalizationIso hU p).hom.hom).map
      (targetStalkLocalizationIso hU p).inv.hom = s := by
    rw [List.map_map]
    change s.map (fun r => (targetStalkLocalizationIso hU p).inv
      ((targetStalkLocalizationIso hU p).hom r)) = s
    simp only [Iso.hom_inv_id_apply]
    exact List.map_id s
  change Module.length (Localization.AtPrime p.asIdeal)
      ((Koszul.finiteProjectionSource (Localization.AtPrime p.asIdeal)
        (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
        (s.map (targetStalkLocalizationIso hU p).hom.hom)
        (originalWholeLocalizedComplex f hU p K)).homology n) =
    Module.length (Y.presheaf.stalk (hU.fromSpec p))
      ((HomologicalComplex.tensorObj
        (Koszul.chainComplex ((s.map (targetStalkLocalizationIso hU p).hom.hom).map
          (targetStalkLocalizationIso hU p).inv.hom))
        (originalPushforwardStalkComplex f hU p K)).homology n) at h
  rw [hl] at h
  exact h

/-- Each actual localized Koszul tensor has exactly the original source-stalk lengths,
with the same equations mapped by the actual finite-map stalk homomorphism. -/
theorem originalFiberKoszul_homology_length
    (s : List (Y.presheaf.stalk (hU.fromSpec p))) (n : ℕ) :
    Module.length (Localization.AtPrime q.asIdeal)
      ((Koszul.finiteProjectionLocal (Localization.AtPrime p.asIdeal)
        (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
        (s.map (targetStalkLocalizationIso hU p).hom.hom)
        (originalWholeLocalizedComplex f hU p K) q).homology n) =
      Module.length (X.presheaf.stalk (wholeAlgebraFiberEquiv f hU p q).1)
        ((originalFiberKoszul f hU p K s (wholeAlgebraFiberEquiv f hU p q)).homology n) := by
  let R := Localization.AtPrime p.asIdeal
  let T := FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
  let Q := Localization.AtPrime q.asIdeal
  let t := s.map (targetStalkLocalizationIso hU p).hom.hom
  have hm : (t.map (algebraMap R T)).map (algebraMap T Q) = t.map (algebraMap R Q) := by
    rw [List.map_map, ← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq R T Q]
  have hl : (((t.map (algebraMap R T)).map (algebraMap T Q)).map
      (originalSourceLocalizationIso f hU p q).hom.hom) =
        s.map (originalFiberStalkMap f hU p (wholeAlgebraFiberEquiv f hU p q)).hom :=
    (congrArg (fun z => z.map (originalSourceLocalizationIso f hU p q).hom.hom) hm).trans
      (originalSourceLocalizationIso_list f hU p q s)
  have h := koszulTransportLength
    (originalSourceLocalizationIso f hU p q).commRingCatIsoToRingEquiv
    ((t.map (algebraMap R T)).map (algebraMap T Q)) (originalWholeSourceIso f hU p K q) n
  change Module.length Q
      ((Koszul.finiteProjectionLocal R T t (originalWholeLocalizedComplex f hU p K) q).homology n) =
    Module.length (X.presheaf.stalk (wholeAlgebraFiberEquiv f hU p q).1)
      ((HomologicalComplex.tensorObj
        (Koszul.chainComplex (((t.map (algebraMap R T)).map (algebraMap T Q)).map
          (originalSourceLocalizationIso f hU p q).hom.hom))
        (originalSourceStalkComplex K (wholeAlgebraFiberEquiv f hU p q).1)).homology n) at h
  exact h.trans (congrArg (fun v : List
      (X.presheaf.stalk (wholeAlgebraFiberEquiv f hU p q).1) =>
    Module.length (X.presheaf.stalk (wholeAlgebraFiberEquiv f hU p q).1)
      ((HomologicalComplex.tensorObj (Koszul.chainComplex v)
        (originalSourceStalkComplex K (wholeAlgebraFiberEquiv f hU p q).1)).homology n)) hl)

private theorem koszulFinite_of_length_eq {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (hC : FiniteHomology C)
    (h : ∀ n, Module.length R (C.homology n) = Module.length T (D.homology n)) :
    FiniteHomology D where
  finite_length n := by rw [← h n]; exact hC.finite_length n
  finite_support := by simpa only [show (fun n => Module.length R (C.homology n)) =
    (fun n => Module.length T (D.homology n)) from funext h] using hC.finite_support

private theorem koszulEuler_eq_of_length_eq {R T : Type u} [CommRing R] [CommRing T]
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {D : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ n, Module.length R (C.homology n) = Module.length T (D.homology n))
    (hC : FiniteHomology C) (hD : FiniteHomology D) : chainEuler C hC = chainEuler D hD := by
  unfold chainEuler homologyEuler signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, h n]

variable [IsNoetherianRing (Y.presheaf.stalk (hU.fromSpec p))]

/-- The original target Koszul homology is finite, derived only from the actual whole total. -/
theorem originalPushforwardKoszul_finiteHomology
    (s : List (Y.presheaf.stalk (hU.fromSpec p)))
    (hK : FiniteHomology (originalWholeKoszulTotal f hU p K s)) :
    FiniteHomology (originalPushforwardKoszul f hU p K s) := by
  have := coordinateFinite f hU
  have := coordinateLocal_noetherian hU p
  exact koszulFinite_of_length_eq
    (Koszul.finiteProjectionSource_finiteHomology (Localization.AtPrime p.asIdeal)
      (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
      (s.map (targetStalkLocalizationIso hU p).hom.hom)
      (originalWholeLocalizedComplex f hU p K) hK)
    (originalPushforwardKoszul_homology_length f hU p K s)

/-- The original source Koszul homology is finite at every maximal point of the whole algebra. -/
theorem originalMaximalKoszul_finiteHomology
    (s : List (Y.presheaf.stalk (hU.fromSpec p)))
    (hK : FiniteHomology (originalWholeKoszulTotal f hU p K s)) :
    FiniteHomology (originalFiberKoszul f hU p K s (wholeAlgebraFiberEquiv f hU p q)) := by
  have := coordinateFinite f hU
  have := coordinateLocal_noetherian hU p
  exact koszulFinite_of_length_eq
    (Koszul.finiteProjectionLocal_finiteHomology (Localization.AtPrime p.asIdeal)
      (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
      (s.map (targetStalkLocalizationIso hU p).hom.hom)
      (originalWholeLocalizedComplex f hU p K) hK q)
    (originalFiberKoszul_homology_length f hU p K q s)

/-- The original Koszul homology is finite on every point of the complete original source fiber. -/
theorem originalFiberKoszul_finiteHomology
    (s : List (Y.presheaf.stalk (hU.fromSpec p)))
    (hK : FiniteHomology (originalWholeKoszulTotal f hU p K s))
    (x : {x : X // f x = hU.fromSpec p}) :
    FiniteHomology (originalFiberKoszul f hU p K s x) := by
  have hx := (wholeAlgebraFiberEquiv f hU p).apply_symm_apply x
  have h := originalMaximalKoszul_finiteHomology f hU p K
    ((wholeAlgebraFiberEquiv f hU p).symm x) s hK
  exact (congrArg (fun z => FiniteHomology (originalFiberKoszul f hU p K s z)) hx).mp h

/-- Actual target-stalk Koszul projection for a genuine global finite morphism.
The equations act through the literal original stalk maps at every point of the
whole source fiber. Only homology of the whole localized Koszul total is assumed finite. -/
theorem originalFinitePushforwardKoszulEuler
    (s : List (Y.presheaf.stalk (hU.fromSpec p)))
    (hK : FiniteHomology (originalWholeKoszulTotal f hU p K s)) :
    chainEuler (originalPushforwardKoszul f hU p K s)
        (originalPushforwardKoszul_finiteHomology f hU p K s hK) =
      ∑ᶠ x : {x : X // f x = hU.fromSpec p}, (f.residueDegree x.1 : ℤ) *
        chainEuler (originalFiberKoszul f hU p K s x)
          (originalFiberKoszul_finiteHomology f hU p K s hK x) := by
  have := coordinateFinite f hU
  have := coordinateLocal_noetherian hU p
  let R := Localization.AtPrime p.asIdeal
  let T := FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
  let t := s.map (targetStalkLocalizationIso hU p).hom.hom
  let C := originalWholeLocalizedComplex f hU p K
  have hC := Koszul.finiteProjectionSource_finiteHomology R T t C hK
  have hq := Koszul.finiteProjectionLocal_finiteHomology R T t C hK
  calc
    _ = chainEuler (Koszul.finiteProjectionSource R T t C) hC :=
      (koszulEuler_eq_of_length_eq (originalPushforwardKoszul_homology_length f hU p K s)
        _ _).symm
    _ = ∑ᶠ q : MaximalSpectrum T, (LocalLength.finiteAlgebraResidueDegree R T q : ℤ) *
        chainEuler (Koszul.finiteProjectionLocal R T t C q) (hq q) :=
      Koszul.finiteProjection_chainEuler_finsum R T t C hK
    _ = ∑ᶠ q : MaximalSpectrum T, (f.residueDegree (wholeAlgebraFiberEquiv f hU p q).1 : ℤ) *
        chainEuler (originalFiberKoszul f hU p K s (wholeAlgebraFiberEquiv f hU p q))
          (originalFiberKoszul_finiteHomology f hU p K s hK
            (wholeAlgebraFiberEquiv f hU p q)) := by
      apply finsum_congr
      intro q
      rw [wholeAlgebra_residueDegree f hU p q]
      congr 1
      exact koszulEuler_eq_of_length_eq (originalFiberKoszul_homology_length f hU p K q s) _ _
    _ = _ := finsum_comp_equiv (wholeAlgebraFiberEquiv f hU p)
      (f := fun x => (f.residueDegree x.1 : ℤ) *
        chainEuler (originalFiberKoszul f hU p K s x)
          (originalFiberKoszul_finiteHomology f hU p K s hK x))

end Motivic.RelativeFiniteSchemeEuler
