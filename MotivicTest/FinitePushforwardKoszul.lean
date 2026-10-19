/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.Koszul
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists
public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyPlacement

/-!
# Actual common-middle-list and global Koszul projection consumers

The remaining middle equations act through the genuine finite image-product
stalk map. The whole localized coefficient is retained at every branch. A
separate genuine tilde contraction supplies the sole total-finiteness premise
for arbitrary original module complexes and arbitrary finite target-stalk lists.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex

universe u

namespace Motivic.MotivicTest.FinitePushforwardKoszul
open _root_.AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

section Correspondence

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]
  {U : (F.leftIntermediateImageProduct G H).Opens} (hU : IsAffineOpen U)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, U))
  (K : ChainComplex (F.leftIntermediateSupportProduct G H).Modules ℕ)
  [∀ n, (K.X n).IsQuasicoherent]

/-- The common remaining middle list comes from the actual image-product middle map. -/
abbrev remainingTargetList
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (hU.fromSpec p)))) :=
  s.map ((F.leftImageMiddlePair G H).stalkMap (hU.fromSpec p)).hom

/-- The actual image-product whole coordinate algebra uses its original section map. -/
local instance imageCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, U)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) :=
  ((F.leftIntermediateImageMap G H).app U).hom.toAlgebra

/-- The common remaining middle list has exactly the same image through whole localization
and through the original image-product scheme stalk map. -/
theorem actualRemainingScalarSquare
    (q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra
        Γ(F.leftIntermediateImageProduct G H, U)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) p))
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (hU.fromSpec p)))) :
    (((remainingTargetList F G H hU p s).map (targetStalkLocalizationIso hU p).hom.hom).map
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))).map
        (originalSourceLocalizationIso (F.leftIntermediateImageMap G H) hU p q).hom.hom =
      (remainingTargetList F G H hU p s).map
        (originalFiberStalkMap (F.leftIntermediateImageMap G H) hU p
          (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) hU p q)).hom :=
  originalSourceLocalizationIso_list _ hU p q _

/-- The constructed actual first-stage source comparison preserves the original differentials. -/
theorem actualSourceDifferential
    (q : MaximalSpectrum (_root_.PrimeSpectrum.FiniteFiber.localAlgebra
        Γ(F.leftIntermediateImageProduct G H, U)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) p))
    (n m : ℕ) :
    let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, U)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) p
    let C := finiteAlgebraLocalizedComplex T
      (originalWholeLocalizedComplex (F.leftIntermediateImageMap G H) hU p K) q
    let D := (Functor.mapHomologicalComplex (ModuleCat.restrictScalars
      (originalSourceLocalizationIso (F.leftIntermediateImageMap G H) hU p q).hom.hom) _).obj
      (originalSourceStalkComplex K
        (FiniteAffineChart.sourceChart (F.leftIntermediateImageMap G H) hU
          (wholeAlgebraSourcePoint (F.leftIntermediateImageMap G H) hU p q).1))
    let e : C ≅ D := originalWholeSourceIso (F.leftIntermediateImageMap G H) hU p K q
    e.hom.f n ≫ D.d n m = C.d n m ≫ e.hom.f m :=
  (originalWholeSourceIso (F.leftIntermediateImageMap G H) hU p K q).hom.comm n m

variable [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (hU.fromSpec p))]

/-- The genuine finite image-product map satisfies Koszul projection for its
original common remaining-middle list, with no coefficient-sheaf existence assumption. -/
theorem actualRemainingProjection
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (hU.fromSpec p))))
    (hK : FiniteHomology (originalWholeKoszulTotal (F.leftIntermediateImageMap G H) hU p K
      (remainingTargetList F G H hU p s))) :
    chainEuler (originalPushforwardKoszul (F.leftIntermediateImageMap G H) hU p K
        (remainingTargetList F G H hU p s))
      (originalPushforwardKoszul_finiteHomology _ hU p K _ hK) =
    ∑ᶠ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p},
      ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        chainEuler (originalFiberKoszul (F.leftIntermediateImageMap G H) hU p K
          (remainingTargetList F G H hU p s) x)
          (originalFiberKoszul_finiteHomology _ hU p K _ hK x) :=
  originalFinitePushforwardKoszulEuler _ hU p K _ hK

/-- Repeated zero equations need no regularity or nonempty-list side premise. -/
theorem actualRepeatedZeroProjection
    (hK : FiniteHomology
      (originalWholeKoszulTotal (F.leftIntermediateImageMap G H) hU p K [0, 0])) :
    chainEuler (originalPushforwardKoszul (F.leftIntermediateImageMap G H) hU p K [0, 0])
      (originalPushforwardKoszul_finiteHomology _ hU p K [0, 0] hK) =
    ∑ᶠ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p},
      ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        chainEuler (originalFiberKoszul (F.leftIntermediateImageMap G H) hU p K [0, 0] x)
          (originalFiberKoszul_finiteHomology _ hU p K [0, 0] hK x) :=
  originalFinitePushforwardKoszulEuler _ hU p K [0, 0] hK

end Correspondence

section Contractible

variable (B : CommRingCat.{u}) {Y : Scheme.{u}} (f : Spec B ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The whole coefficient algebra has the original finite-map section action. -/
local instance coordinateAlgebra : Algebra Γ(Y, U) Γ(Spec B, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

local instance sourceTilde_additive : (tilde.functor B).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual tilde of the scalar-one tensor of an unrestricted original complex. -/
abbrev unitTildeComplex (L : ChainComplex (ModuleCat.{u} B) ℕ) :=
  ((tilde.functor B).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (tensorObj (_root_.ChainComplex.Koszul.singleComplex B 1) L)

/-- Every original term is genuinely quasi-coherent. -/
instance unitTildeComplex_quasicoherent (L : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    ((unitTildeComplex B L).X n).IsQuasicoherent :=
  inferInstanceAs
    (((tilde.functor B).obj ((tensorObj (_root_.ChainComplex.Koszul.singleComplex B 1) L).X
        n)).IsQuasicoherent)

/-- The original contraction maps through the actual whole affine chart and its localization. -/
def wholeUnitHomotopy (L : ChainComplex (ModuleCat.{u} B) ℕ) :
    Homotopy (𝟙 (originalWholeLocalizedComplex f hU p (unitTildeComplex B L))) 0 := by
  have : (Scheme.Modules.restrictFunctor (FiniteAffineChart.sourceChart f hU)).Additive :=
    Functor.additive_of_iso
      (Scheme.Modules.restrictFunctorIsoPullback (FiniteAffineChart.sourceChart f hU)).symm
  let E := tilde.functor B ⋙
    Scheme.Modules.restrictFunctor (FiniteAffineChart.sourceChart f hU) ⋙
    moduleSpecΓFunctor ⋙ ModuleCat.extendScalars
      (algebraMap Γ(Spec B, f ⁻¹ᵁ U)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(Y, U) Γ(Spec B, f ⁻¹ᵁ U) p))
  exact (Homotopy.ofEq ((E.mapHomologicalComplex _).map_id _).symm).trans
    ((E.mapHomotopy (_root_.ChainComplex.Koszul.singleUnitTensorHomotopy L)).trans
      (Homotopy.ofEq ((E.mapHomologicalComplex _).map_zero _ _)))

/-- Every finite target-stalk list preserves the constructed contraction on the
whole localized coefficient; the original unrestricted complex needs no finiteness. -/
theorem contractedWholeKoszulFinite (L : ChainComplex (ModuleCat.{u} B) ℕ)
    (s : List (Y.presheaf.stalk (hU.fromSpec p))) :
    FiniteHomology (originalWholeKoszulTotal f hU p (unitTildeComplex B L) s) := by
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(Y, U) Γ(Spec B, f ⁻¹ᵁ U) p
  let C := originalWholeLocalizedComplex f hU p (unitTildeComplex B L)
  let D := _root_.ChainComplex.Koszul.chainComplex ((s.map (targetStalkLocalizationIso hU
      p).hom.hom).map
    (algebraMap (Localization.AtPrime p.asIdeal) T))
  have hc := (mapBifunctorMapHomotopy₂ (𝟙 D) (wholeUnitHomotopy B f hU p L)
    (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat T)) (ComplexShape.down ℕ)).trans
      (Homotopy.ofEq (_root_.ChainComplex.Koszul.tensorHom_zero_right D C))
  have hid : tensorHom (𝟙 D) (𝟙 C) = 𝟙 (tensorObj D C) := by
    simpa only [one_smul] using _root_.ChainComplex.Koszul.tensorHom_scalar_right D C (1 : T)
  exact _root_.ChainComplex.Koszul.finiteHomology_of_identity_homotopy _ ((Homotopy.ofEq
      hid.symm).trans hc)

variable [IsNoetherianRing (Y.presheaf.stalk (hU.fromSpec p))]

/-- The actual global Koszul formula consumes a constructed whole-total finiteness
proof for arbitrary lists, including empty or repeated-zero lists, and arbitrary original L. -/
theorem contractedGlobalProjection (L : ChainComplex (ModuleCat.{u} B) ℕ)
    (s : List (Y.presheaf.stalk (hU.fromSpec p))) :
    chainEuler (originalPushforwardKoszul f hU p (unitTildeComplex B L) s)
      (originalPushforwardKoszul_finiteHomology f hU p _ s
        (contractedWholeKoszulFinite B f hU p L s)) =
    ∑ᶠ x : {x : Spec B // f x = hU.fromSpec p}, (f.residueDegree x.1 : ℤ) *
      chainEuler (originalFiberKoszul f hU p (unitTildeComplex B L) s x)
        (originalFiberKoszul_finiteHomology f hU p _ s
          (contractedWholeKoszulFinite B f hU p L s) x) :=
  originalFinitePushforwardKoszulEuler f hU p _ s (contractedWholeKoszulFinite B f hU p L s)

end Contractible

end Motivic.MotivicTest.FinitePushforwardKoszul
