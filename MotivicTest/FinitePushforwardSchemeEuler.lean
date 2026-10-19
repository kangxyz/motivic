/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.SchemeEuler
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists
public import Motivic.Aglib.Algebra.Homology.Koszul.HyperhomologyPlacement

/-!
# Genuine global finite-pushforward numerical consumers

The actual finite image-product map is used on a given QC complex with only
whole-local finite homology. Separately, a genuine scalar-one tilde complex
constructs the local finiteness premise from its contraction, with unrestricted
original module-complex terms. No first-stage Tor sheaf is presumed to exist.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry HomologicalComplex

universe u

namespace Motivic.MotivicTest.FinitePushforwardSchemeEuler
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
  [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (hU.fromSpec p))]

/-- The original global finite image-product pushforward has the residue-weighted
Euler formula over every original source point, under only whole local finite homology. -/
theorem actualImageProductEuler
    (hK : FiniteHomology (originalWholeLocalizedComplex (F.leftIntermediateImageMap G H) hU p K)) :
    chainEuler (originalPushforwardStalkComplex (F.leftIntermediateImageMap G H) hU p K)
        (originalPushforward_finiteHomology _ hU p K hK) =
      ∑ᶠ x : {x : F.leftIntermediateSupportProduct G H //
          F.leftIntermediateImageMap G H x = hU.fromSpec p},
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
          chainEuler (originalSourceStalkComplex K x.1)
            (originalFiber_finiteHomology _ hU p K hK x) :=
  originalFinitePushforwardChainEuler _ hU p K hK

/-- Local homology finiteness is derived at every original point of the actual
finite image-product fiber, without a separate finite-source-stalk hypothesis. -/
theorem actualImageProductFiberFinite
    (hK : FiniteHomology (originalWholeLocalizedComplex (F.leftIntermediateImageMap G H) hU p K))
    (x : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = hU.fromSpec p}) :
    FiniteHomology (originalSourceStalkComplex K x.1) :=
  originalFiber_finiteHomology _ hU p K hK x

end Correspondence

section Contractible

variable (B : CommRingCat.{u}) {Y : Scheme.{u}} (f : Spec B ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The whole inverse-image algebra uses the original finite-map section homomorphism. -/
local instance coordinateAlgebra : Algebra Γ(Y, U) Γ(Spec B, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

local instance sourceTilde_additive : (tilde.functor B).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A genuine original QC sheaf complex with an explicit scalar-one contraction. -/
abbrev unitTildeComplex (L : ChainComplex (ModuleCat.{u} B) ℕ) :=
  ((tilde.functor B).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (tensorObj (_root_.ChainComplex.Koszul.singleComplex B 1) L)

/-- Each term is the actual quasi-coherent tilde of its original module term. -/
instance unitTildeComplex_quasicoherent (L : ChainComplex (ModuleCat.{u} B) ℕ) (n : ℕ) :
    ((unitTildeComplex B L).X n).IsQuasicoherent :=
  inferInstanceAs
    (((tilde.functor B).obj ((tensorObj (_root_.ChainComplex.Koszul.singleComplex B 1) L).X
        n)).IsQuasicoherent)

/-- The actual whole-chart localization carries the mapped original contraction.
No finite-length, finite-generation, boundedness or homology premise is placed on L. -/
theorem contractibleTildeWholeFinite (L : ChainComplex (ModuleCat.{u} B) ℕ) :
    FiniteHomology (originalWholeLocalizedComplex f hU p (unitTildeComplex B L)) := by
  have : (Scheme.Modules.restrictFunctor (FiniteAffineChart.sourceChart f hU)).Additive :=
    Functor.additive_of_iso
      (Scheme.Modules.restrictFunctorIsoPullback (FiniteAffineChart.sourceChart f hU)).symm
  let F := tilde.functor B ⋙ Scheme.Modules.restrictFunctor (FiniteAffineChart.sourceChart f hU) ⋙
    moduleSpecΓFunctor ⋙ ModuleCat.extendScalars
      (algebraMap Γ(Spec B, f ⁻¹ᵁ U)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(Y, U) Γ(Spec B, f ⁻¹ᵁ U) p))
  apply _root_.ChainComplex.Koszul.finiteHomology_of_identity_homotopy
  exact (Homotopy.ofEq ((F.mapHomologicalComplex _).map_id _).symm).trans
    ((F.mapHomotopy (_root_.ChainComplex.Koszul.singleUnitTensorHomotopy L)).trans
      (Homotopy.ofEq ((F.mapHomologicalComplex _).map_zero _ _)))

variable [IsNoetherianRing (Y.presheaf.stalk (hU.fromSpec p))]

/-- The original global finite pushforward formula consumes constructed finite
homology for a genuine QC complex, without a finiteness premise on the original L. -/
theorem contractibleGlobalEuler (L : ChainComplex (ModuleCat.{u} B) ℕ) :
    chainEuler (originalPushforwardStalkComplex f hU p (unitTildeComplex B L))
        (originalPushforward_finiteHomology f hU p _ (contractibleTildeWholeFinite B f hU p L)) =
      ∑ᶠ x : {x : Spec B // f x = hU.fromSpec p}, (f.residueDegree x.1 : ℤ) *
        chainEuler (originalSourceStalkComplex (unitTildeComplex B L) x.1)
          (originalFiber_finiteHomology f hU p _ (contractibleTildeWholeFinite B f hU p L) x) :=
  originalFinitePushforwardChainEuler f hU p _ (contractibleTildeWholeFinite B f hU p L)

end Contractible

end Motivic.MotivicTest.FinitePushforwardSchemeEuler
