/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorBounded
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Actual right-first-stage whole Tor finiteness and boundedness

The consumers use the actual finite image-product map, the constructed Tor
coefficient, original supported Tor stalks and original smooth diagonal. All
finiteness and degree bounds are derived. Remaining-Koszul finite length and
support are not asserted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.RightWholeFiberTorBounded
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The actual image-product section map is the coefficient algebra action. -/
local instance actualCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

/-- Original locally finite-type Noetherian geometry proves actual whole coefficient finiteness. -/
theorem actualWholeCoefficient_finite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [LocallyOfFiniteType i] (n : ℕ) :
    Module.Finite (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G
        H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
      (F.rightFirstStageWholeLocalizedCoefficient G H V p n) := by
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  exact wholeFiberTorLocalizedSections_finite _ _ _ _ _ _ _ _ _

/-- Every original fiber point has a geometrically derived right-first-stage Tor bound. -/
theorem actualFiberPoint_bound [Flat f] [Flat g] [Smooth h] [Flat i]
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) :
    ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton ((Stalk.functor x.1).obj
        (F.rightFirstStageWholeAmbientCoefficient G H V n)) :=
  F.rightFirstStageWholeStalk_exists_bound G H V x.1
    (wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V p x)

/-- The actual entire localized coefficient has one bound, with no uniform bound input. -/
theorem actualWholeCoefficient_bound [Flat f] [Flat g] [Smooth h] [Flat i] :
    ∃ b : ℕ, ∀ n, b ≤ n → Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n) :=
  F.rightFirstStageWholeLocalized_exists_bound G H V p

/-- The actual entire coefficient family has finite outer nonzero support. -/
theorem actualWholeCoefficient_support [Flat f] [Flat g] [Smooth h] [Flat i] :
    {n : ℕ | ¬ Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)}.Finite :=
  F.rightFirstStageWholeLocalized_nonzero_finite G H V p

section Smooth

variable (K : Type u) [Field K] (X Y Z W : SmoothSite (Spec (.of K)))
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- Smooth-site triples over every field satisfy actual whole finiteness in each Tor degree. -/
theorem actualSmoothWholeCoefficient_finite (n : ℕ) :
    letI : Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
        ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra
    Module.Finite (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G
        H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p)
      (F.rightFirstStageWholeLocalizedCoefficient (S := Spec (.of K)) G H V p n) :=
  actualWholeCoefficient_finite (S := Spec (.of K)) F G H V p n

/-- The smooth-site application derives its whole outer bound without a chosen dimension. -/
theorem actualSmoothWholeCoefficient_bound :
    ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (F.rightFirstStageWholeLocalizedCoefficient (S := Spec (.of K)) G H V p n) :=
  F.rightFirstStageWholeLocalized_exists_bound (S := Spec (.of K)) G H V p

end Smooth

end Motivic.MotivicTest.RightWholeFiberTorBounded
