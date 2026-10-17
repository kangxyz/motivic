/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorCoefficient
public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorChartStalk

/-!
# Original stalks of the actual whole-fiber Tor coefficient

The actual finite-cover equalizer and its genuine chart comparisons identify
the original stalk of the constructed whole-preimage coefficient with existing
supported geometric Tor. A chart is selected from the proved original covering,
not supplied as an assumed stalk equivalence. All changes of scalars use the
actual open inclusion stalk maps. Finite generation does not assert finite
length or global finite generation of all affine sections.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.ModuleStalk

/-- Open restriction recovers the original stalk after restriction along the
actual open immersion structure-stalk map. -/
def openRestrictionOriginalIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
      ((functor x).obj ((Scheme.Modules.restrictFunctor f).obj M)) ≅
        (functor (f x)).obj M :=
  (ModuleCat.restrictScalars (f.stalkMap x).hom).mapIso
    ((openRestrictionIso f x).app M) ≪≫
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).counitIso.app _

end Motivic.ModuleStalk

namespace Motivic.Intersection

private theorem finite_of_restrictScalarsIso {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) (M : ModuleCat.{u} S) (N : ModuleCat.{u} R) [Module.Finite R N]
    (e : (ModuleCat.restrictScalars g).obj M ≅ N) : Module.Finite S M := by
  let l : N →ₛₗ[g] M :=
    { __ := e.inv.hom.toAddMonoidHom
      map_smul' := e.inv.hom.map_smul }
  exact Module.Finite.of_surjective l
    ((ModuleCat.epi_iff_surjective e.inv).mp inferInstance)

variable {P T D W Y : Scheme.{u}} [P.IsSeparated]
  (i : T ⟶ P) (j : D ⟶ P) (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b j i)

/-- The original stalk of the actual finite compatible-sections equalizer is
supported geometric Tor at every point belonging to an original chart. -/
def closedIntersectionTorGluedStalkIso {ι : Type u} [Fintype ι]
    (U : ι → P.affineOpens) (r : ι) (w : W) (hw : (a ≫ j) w ∈ (U r).1) (n : ℕ) :
    (ModuleStalk.functor w).obj (closedIntersectionTorGlued i j a b sq U n) ≅
      closedIntersectionSupportedStalkTor j i a b sq w n :=
  (ModuleStalk.openRestrictionOriginalIso ((a ≫ j) ⁻¹ᵁ U r).ι ⟨w, hw⟩
    (closedIntersectionTorGlued i j a b sq U n)).symm ≪≫
      (ModuleCat.restrictScalars (((a ≫ j) ⁻¹ᵁ U r).ι.stalkMap ⟨w, hw⟩).hom).mapIso
        ((ModuleStalk.functor (X := ((a ≫ j) ⁻¹ᵁ U r).toScheme) ⟨w, hw⟩).mapIso
          (closedIntersectionTorGluedLocalIso i j a b sq U n r)) ≪≫
            closedIntersectionTorChartStalkIso j i a b sq (U r) w hw n

variable (f : W ⟶ Y) [IsFinite f] (V : Y.affineOpens)

/-- The proved whole-preimage cover supplies an original Tor chart at every
point; the actual equalizer stalk is therefore the existing supported Tor. -/
def wholeFiberTorGluedStalkIso (w : W) (hw : w ∈ f ⁻¹ᵁ V) (n : ℕ) :
    (ModuleStalk.functor w).obj (closedIntersectionTorGlued i j a b sq
      (wholeFiberTorAmbientFamily i j a b sq f V) n) ≅
        closedIntersectionSupportedStalkTor j i a b sq w n := by
  let r := Classical.choose (wholeFiberTorCoefficient_chart_at i j a b sq f V hw)
  have hr := Classical.choose_spec (wholeFiberTorCoefficient_chart_at i j a b sq f V hw)
  exact closedIntersectionTorGluedStalkIso i j a b sq
    (wholeFiberTorAmbientFamily i j a b sq f V) r w hr n

/-- The actual whole-coefficient stalk has its original structure-stalk action;
the supported Tor target is restricted through the inverse original inclusion. -/
def wholeFiberTorCoefficientStalkIso (x : (f ⁻¹ᵁ V).toScheme) (n : ℕ) :
    (ModuleStalk.functor x).obj (wholeFiberTorCoefficient i j a b sq f V n) ≅
      (ModuleCat.restrictScalars (inv ((f ⁻¹ᵁ V).ι.stalkMap x)).hom).obj
        (closedIntersectionSupportedStalkTor j i a b sq x.1 n) :=
  (ModuleStalk.openRestrictionIso (f ⁻¹ᵁ V).ι x).app _ ≪≫
    (ModuleCat.restrictScalars (inv ((f ⁻¹ᵁ V).ι.stalkMap x)).hom).mapIso
      (wholeFiberTorGluedStalkIso i j a b sq f V x.1 x.2 n)

/-- Over the original intersection local ring, the exact whole-coefficient stalk
attachment uses the literal original open-inclusion stalk map. -/
def wholeFiberTorCoefficientOriginalStalkIso (x : (f ⁻¹ᵁ V).toScheme) (n : ℕ) :
    (ModuleCat.restrictScalars ((f ⁻¹ᵁ V).ι.stalkMap x).hom).obj
      ((ModuleStalk.functor x).obj (wholeFiberTorCoefficient i j a b sq f V n)) ≅
        closedIntersectionSupportedStalkTor j i a b sq x.1 n :=
  ModuleStalk.openRestrictionOriginalIso (f ⁻¹ᵁ V).ι x _ ≪≫
    wholeFiberTorGluedStalkIso i j a b sq f V x.1 x.2 n

/-- Every original equalizer stalk on the covered whole inverse image is finite,
without any global quasi-coherence claim for that equalizer. -/
theorem wholeFiberTorGluedStalk_finite [IsLocallyNoetherian P]
    (w : W) (hw : w ∈ f ⁻¹ᵁ V) (n : ℕ) :
    Module.Finite (W.presheaf.stalk w)
      ((ModuleStalk.functor w).obj (closedIntersectionTorGlued i j a b sq
        (wholeFiberTorAmbientFamily i j a b sq f V) n)) := by
  obtain ⟨r, hr⟩ := wholeFiberTorCoefficient_chart_at i j a b sq f V hw
  let U := wholeFiberTorAmbientFamily i j a b sq f V r
  let := IsLocallyNoetherian.component_noetherian U
  have := closedIntersectionSupportedStalkTor_finite j i a b sq U w hr n
  let e := wholeFiberTorGluedStalkIso i j a b sq f V w hw n
  exact Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap
    e.symm.toLinearEquiv.surjective

/-- Every genuine stalk of the actual whole coefficient is finitely generated
under the original locally Noetherian ambient hypothesis. -/
theorem wholeFiberTorCoefficientStalk_finite [IsLocallyNoetherian P]
    (x : (f ⁻¹ᵁ V).toScheme) (n : ℕ) :
    Module.Finite ((f ⁻¹ᵁ V).toScheme.presheaf.stalk x)
      ((ModuleStalk.functor x).obj (wholeFiberTorCoefficient i j a b sq f V n)) := by
  obtain ⟨r, hr⟩ := wholeFiberTorCoefficient_chart_at i j a b sq f V x.2
  let U := wholeFiberTorAmbientFamily i j a b sq f V r
  let := IsLocallyNoetherian.component_noetherian U
  have : Module.Finite (W.presheaf.stalk ((f ⁻¹ᵁ V).ι x))
      (closedIntersectionSupportedStalkTor j i a b sq x.1 n) :=
    closedIntersectionSupportedStalkTor_finite j i a b sq U x.1 hr n
  exact finite_of_restrictScalarsIso ((f ⁻¹ᵁ V).ι.stalkMap x).hom _ _
    (wholeFiberTorCoefficientOriginalStalkIso i j a b sq f V x n)

end Motivic.Intersection
