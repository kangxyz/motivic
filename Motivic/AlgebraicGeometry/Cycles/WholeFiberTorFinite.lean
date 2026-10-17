/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardRelative
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorStalk

/-!
# Finite whole localized coefficients for the actual glued Tor sheaf

The genuine finite-cover Tor equalizer has proved QC only on the whole finite
inverse image. Its actual original stalks are finite supported Tor modules.
The relative semilocal criterion therefore proves finite generation of the
whole localized coefficient, including all original source branches. An actual
coordinate isomorphism also identifies the original constructed section module.
Finite length and remaining-Koszul support are separate obligations.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Intersection

open Scheme.Modules FiniteSchemeEuler

variable {P T D W Y : Scheme.{u}} [P.IsSeparated]
  (i : T ⟶ P) (j : D ⟶ P) (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b j i)
  (f : W ⟶ Y) [IsFinite f] (V : Y.affineOpens) (p : Spec Γ(Y, V))

/-- The whole coefficient algebra uses the original finite-map section homomorphism. -/
local instance wholeTorCoordinateAlgebra : Algebra Γ(Y, V) Γ(W, f ⁻¹ᵁ V) :=
  (f.app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual ambient equalizer is quasi-coherent on the entire inverse image,
as proved by its genuine finite-cover descent. -/
instance wholeFiberTorGlued_relativeQuasicoherent (n : ℕ) :
    ((restrictFunctor (f ⁻¹ᵁ V).ι).obj
      (closedIntersectionTorGlued i j a b sq
        (wholeFiberTorAmbientFamily i j a b sq f V) n)).IsQuasicoherent :=
  wholeFiberTorCoefficient_quasicoherent i j a b sq f V n

/-- The original whole-chart coordinate module identifies the actual section
module of the constructed whole-preimage coefficient by restriction composition. -/
def wholeFiberTorCoordinateModuleIso (n : ℕ) :
    originalCoordinateModule f V.2
        (closedIntersectionTorGlued i j a b sq (wholeFiberTorAmbientFamily i j a b sq f V) n) ≅
      wholeFiberTorSectionModule i j a b sq f V n :=
  moduleSpecΓFunctor.mapIso
    ((RelativeAffineQuasicoherent.sourceChartRestrictionIso f V.2).app _)

/-- Localization of the actual constructed whole-section module at the target prime. -/
abbrev wholeFiberTorLocalizedSections (n : ℕ) :=
  (ModuleCat.extendScalars
    (algebraMap Γ(W, f ⁻¹ᵁ V) (FiniteFiber.localAlgebra Γ(Y, V) Γ(W, f ⁻¹ᵁ V) p))).obj
      (wholeFiberTorSectionModule i j a b sq f V n)

/-- The relative finite-pushforward coefficient is the localization of the actual
constructed section module, with the same whole finite-algebra action. -/
def wholeFiberTorLocalizedSectionsIso (n : ℕ) :
    originalWholeLocalizedModule f V.2 p
        (closedIntersectionTorGlued i j a b sq (wholeFiberTorAmbientFamily i j a b sq f V) n) ≅
      wholeFiberTorLocalizedSections i j a b sq f V p n :=
  (ModuleCat.extendScalars
    (algebraMap Γ(W, f ⁻¹ᵁ V) (FiniteFiber.localAlgebra Γ(Y, V) Γ(W, f ⁻¹ᵁ V) p))).mapIso
      (wholeFiberTorCoordinateModuleIso i j a b sq f V n)

omit [IsFinite f] in
/-- Every original point of the complete source fiber belongs to the actual whole open. -/
theorem wholeFiberTor_source_mem (x : {w : W // f w = V.2.fromSpec p}) : x.1 ∈ f ⁻¹ᵁ V := by
  change f x.1 ∈ V.1
  rw [x.2]
  exact V.2.range_fromSpec.subset (Set.mem_range_self p)

/-- Actual supported Tor stalk finiteness gives finite generation of the entire
original localized coefficient, without any global QC assumption. -/
theorem wholeFiberTorLocalizedModule_finite [IsLocallyNoetherian P] (n : ℕ) :
    Module.Finite (FiniteFiber.localAlgebra Γ(Y, V) Γ(W, f ⁻¹ᵁ V) p)
      (originalWholeLocalizedModule f V.2 p
        (closedIntersectionTorGlued i j a b sq (wholeFiberTorAmbientFamily i j a b sq f V) n)) :=
  RelativeFiniteSchemeEuler.originalWholeModule_finite f V.2 p _
    (fun x => wholeFiberTorGluedStalk_finite i j a b sq f V x.1
      (wholeFiberTor_source_mem f V p x) n)

/-- The genuine whole-section coefficient itself is finite after localization;
the premise is original locally Noetherian geometry, not assumed finite sections. -/
theorem wholeFiberTorLocalizedSections_finite [IsLocallyNoetherian P] (n : ℕ) :
    Module.Finite (FiniteFiber.localAlgebra Γ(Y, V) Γ(W, f ⁻¹ᵁ V) p)
      (wholeFiberTorLocalizedSections i j a b sq f V p n) := by
  have := wholeFiberTorLocalizedModule_finite i j a b sq f V p n
  let e := wholeFiberTorLocalizedSectionsIso i j a b sq f V p n
  exact Module.Finite.of_surjective e.toLinearEquiv.toLinearMap e.toLinearEquiv.surjective

end Motivic.Intersection
