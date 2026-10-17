/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardSemilocal
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists

/-!
# Actual whole-fiber finite-generation and zero-detection consumers

The correct finite image-product map consumes actual original source stalks.
A separate tilde consumer derives all of those stalk finiteness witnesses from
a genuinely finite original coordinate module. No finite-length premise occurs.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.FinitePushforwardSemilocal

open FiniteSchemeEuler

/-- Every whole coordinate coefficient uses the original finite-map section action. -/
local instance coordinateAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Correspondence

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]
  {U : (F.leftIntermediateImageProduct G H).Opens} (hU : IsAffineOpen U)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, U))
  (N : (F.leftIntermediateSupportProduct G H).Modules) [N.IsQuasicoherent]

/-- Finite generation on the actual full source fiber gives one finite whole coefficient. -/
theorem actualImageProductFinite
    (hN : ∀ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p},
      Module.Finite ((F.leftIntermediateSupportProduct G H).presheaf.stalk x.1)
        (originalSourceStalkModule N x.1)) :
    Module.Finite
      (FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, U)
        Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ U) p)
      (originalWholeLocalizedModule (F.leftIntermediateImageMap G H) hU p N) :=
  originalWholeModule_finite _ hU p N hN

/-- Actual full-fiber stalk vanishing detects the whole coefficient for the correct finite map. -/
theorem actualImageProductZero
    (hN : ∀ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p},
      Subsingleton (originalSourceStalkModule N x.1)) :
    Subsingleton (originalWholeLocalizedModule (F.leftIntermediateImageMap G H) hU p N) :=
  originalWholeModule_subsingleton _ hU p N hN

/-- Empty actual fibers cause no surjectivity exception and need no coefficient finiteness. -/
theorem actualEmptyFiberZero
    [IsEmpty {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = hU.fromSpec p}] :
    Subsingleton (originalWholeLocalizedModule (F.leftIntermediateImageMap G H) hU p N) :=
  originalWholeModule_subsingleton _ hU p N (fun x => isEmptyElim x)

end Correspondence

section Tilde

variable (B : CommRingCat.{u}) (M : ModuleCat.{u} B) [Module.Finite B M]

/-- Actual source tilde stalks are finite over their own original structure-stalk ring. -/
theorem finiteTildeSourceStalk (x : Spec B) :
    Module.Finite ((Spec B).presheaf.stalk x)
      (originalSourceStalkModule ((tilde.functor B).obj M) x) := by
  have : Module.Finite ((Spec B).presheaf.stalk x)
      ((AffinePushforward.stalkTensorFunctor B x).obj M) := by
    change Module.Finite ((Spec B).presheaf.stalk x) ((Spec B).presheaf.stalk x ⊗[B] M)
    infer_instance
  exact Module.Finite.of_surjective
    ((AffinePushforward.tildeStalkIso B x).app M).toLinearEquiv.toLinearMap
    ((AffinePushforward.tildeStalkIso B x).app M).toLinearEquiv.surjective

variable {Y : Scheme.{u}} (f : Spec B ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The actual finite tilde module supplies every source witness; the theorem
constructs finite generation of its whole localized inverse-image coefficient. -/
theorem actualFiniteTildeWhole :
    Module.Finite (FiniteFiber.localAlgebra Γ(Y, U) Γ(Spec B, f ⁻¹ᵁ U) p)
      (originalWholeLocalizedModule f hU p ((tilde.functor B).obj M)) :=
  originalWholeModule_finite f hU p ((tilde.functor B).obj M)
    (fun x => finiteTildeSourceStalk B M x.1)

end Tilde

end Motivic.MotivicTest.FinitePushforwardSemilocal
