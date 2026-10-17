/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedIntersectionTorDescent

/-!
# Actual Tor coefficients on a whole finite inverse image

A finite ambient affine family is chosen from the proved cover of the entire
affine inverse image of a finite morphism. The constructed Tor equalizer is
restricted to that full open and is proved quasi-coherent there. Empty covers
and empty inverse images are allowed. This auxiliary construction depends on
the chosen finite cover; cover-independence, exact stalk comparison, finite
generation of its whole-section module and a uniform degree bound are separate.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.Intersection

open Scheme.Modules ClosedAffineCover

variable {P T D W Y : Scheme.{u}} [P.IsSeparated]
  (i : T ⟶ P) (j : D ⟶ P) (a : W ⟶ D) (b : W ⟶ T)
  [IsClosedImmersion i] [IsClosedImmersion j] (sq : IsPullback a b j i)
  (f : W ⟶ Y) [IsFinite f] (V : Y.affineOpens)

include sq in
omit [P.IsSeparated] in
/-- The actual closed-intersection embedding is closed by its Cartesian construction. -/
theorem closedIntersection_isClosedImmersion : IsClosedImmersion (a ≫ j) := by
  have : IsClosedImmersion a := by
    rw [← sq.isoPullback_hom_fst]
    infer_instance
  infer_instance

/-- A chosen finite ambient affine family covering the entire finite inverse image. -/
def wholeFiberTorAmbientCover : Finset P.affineOpens := by
  let := closedIntersection_isClosedImmersion i j a b sq
  exact Classical.choose (finiteMap_exists_whole_preimage_cover (a ≫ j) f V)

omit [P.IsSeparated] in
/-- Every chosen original chart lies inside the whole inverse image and their union is all of it. -/
theorem wholeFiberTorAmbientCover_spec :
    (∀ U ∈ wholeFiberTorAmbientCover i j a b sq f V,
      (a ≫ j) ⁻¹ᵁ U ≤ f ⁻¹ᵁ V) ∧
    (⨆ U ∈ wholeFiberTorAmbientCover i j a b sq f V, (a ≫ j) ⁻¹ᵁ U) = f ⁻¹ᵁ V := by
  let := closedIntersection_isClosedImmersion i j a b sq
  exact Classical.choose_spec (finiteMap_exists_whole_preimage_cover (a ≫ j) f V)

/-- The original ambient affine associated to each member of the actual chosen finite family. -/
def wholeFiberTorAmbientFamily
    (r : wholeFiberTorAmbientCover i j a b sq f V) : P.affineOpens := r.val

omit [P.IsSeparated] in
/-- The subtype-indexed family still covers precisely the full original inverse image. -/
theorem wholeFiberTorAmbientFamily_cover :
    (⨆ r, (a ≫ j) ⁻¹ᵁ wholeFiberTorAmbientFamily i j a b sq f V r) = f ⁻¹ᵁ V := by
  simpa only [wholeFiberTorAmbientFamily, iSup_subtype] using
    (wholeFiberTorAmbientCover_spec i j a b sq f V).2

/-- The actual coefficient sheaf on the entire finite inverse image. -/
def wholeFiberTorCoefficient (n : ℕ) : (f ⁻¹ᵁ V).toScheme.Modules :=
  closedIntersectionTorCoefficient i j a b sq
    (wholeFiberTorAmbientFamily i j a b sq f V) (f ⁻¹ᵁ V) n

/-- Actual finite-cover descent proves quasi-coherence on every branch of the inverse image. -/
instance wholeFiberTorCoefficient_quasicoherent (n : ℕ) :
    (wholeFiberTorCoefficient i j a b sq f V n).IsQuasicoherent :=
  closedIntersectionTorCoefficient_quasicoherent i j a b sq
    (wholeFiberTorAmbientFamily i j a b sq f V) (f ⁻¹ᵁ V)
      (wholeFiberTorAmbientFamily_cover i j a b sq f V) n

omit [P.IsSeparated] in
/-- Every source point in the whole inverse image belongs to an original ambient Tor chart. -/
theorem wholeFiberTorCoefficient_chart_at {x : W} (hx : x ∈ f ⁻¹ᵁ V) :
    ∃ r : wholeFiberTorAmbientCover i j a b sq f V,
      x ∈ (a ≫ j) ⁻¹ᵁ wholeFiberTorAmbientFamily i j a b sq f V r := by
  rw [← wholeFiberTorAmbientFamily_cover i j a b sq f V] at hx
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- The actual relative comparison recovers each original Tor coefficient on its full chart. -/
def wholeFiberTorCoefficientLocalIso (n : ℕ)
    (r : wholeFiberTorAmbientCover i j a b sq f V) :
    (restrictFunctor ((f ⁻¹ᵁ V).ι ⁻¹ᵁ
      ((a ≫ j) ⁻¹ᵁ wholeFiberTorAmbientFamily i j a b sq f V r)).ι).obj
        (wholeFiberTorCoefficient i j a b sq f V n) ≅
      (restrictFunctor (Scheme.Opens.isoOfLE
        ((wholeFiberTorAmbientCover_spec i j a b sq f V).1 r.val r.property)).hom).obj
          (closedIntersectionTorChartSheaf i a b j sq
            (wholeFiberTorAmbientFamily i j a b sq f V r) n) :=
  FiniteOpenModuleGluing.relativeLocalIso _ _
    (closedIntersectionTorDatum i j a b sq
      (wholeFiberTorAmbientFamily i j a b sq f V) n) (f ⁻¹ᵁ V) r _

/-- The entire inverse image is an actual affine open by finiteness of the original map. -/
def wholeFiberTorAffineOpen : W.affineOpens := ⟨f ⁻¹ᵁ V, V.2.preimage f⟩

/-- The constructed coefficient expressed on the spectrum of its actual affine coordinate ring. -/
def wholeFiberTorSpecCoefficient (n : ℕ) : (Spec Γ(W, f ⁻¹ᵁ V)).Modules :=
  (restrictFunctor (wholeFiberTorAffineOpen f V).2.isoSpec.inv).obj
    (wholeFiberTorCoefficient i j a b sq f V n)

/-- The original affine-chart equivalence preserves the proved whole-preimage quasi-coherence. -/
instance wholeFiberTorSpecCoefficient_quasicoherent (n : ℕ) :
    (wholeFiberTorSpecCoefficient i j a b sq f V n).IsQuasicoherent :=
  @isQuasicoherent_restrictFunctor _ _ (wholeFiberTorAffineOpen f V).2.isoSpec.inv _
    (wholeFiberTorCoefficient i j a b sq f V n)
    (wholeFiberTorCoefficient_quasicoherent i j a b sq f V n)

/-- Actual affine-coordinate global sections of the constructed whole-preimage coefficient. -/
def wholeFiberTorSectionModule (n : ℕ) : ModuleCat.{u} Γ(W, f ⁻¹ᵁ V) :=
  moduleSpecΓFunctor.obj (wholeFiberTorSpecCoefficient i j a b sq f V n)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine affine tilde counit reconstructs the whole finite-preimage coefficient. -/
def wholeFiberTorTildeIso (n : ℕ) :
    (AffineOpenTilde.chartTilde (wholeFiberTorAffineOpen f V)).obj
      (wholeFiberTorSectionModule i j a b sq f V n) ≅
        wholeFiberTorCoefficient i j a b sq f V n :=
  (restrictFunctor (wholeFiberTorAffineOpen f V).2.isoSpec.hom).mapIso
      (@asIso _ _ _ _ (wholeFiberTorSpecCoefficient i j a b sq f V n).fromTildeΓ
        (@isIso_fromTildeΓ_of_isQuasicoherent _
          (wholeFiberTorSpecCoefficient i j a b sq f V n)
          (wholeFiberTorSpecCoefficient_quasicoherent i j a b sq f V n))) ≪≫
    (restrictFunctorComp (wholeFiberTorAffineOpen f V).2.isoSpec.hom
      (wholeFiberTorAffineOpen f V).2.isoSpec.inv).symm.app _ ≪≫
    (restrictFunctorCongr (wholeFiberTorAffineOpen f V).2.isoSpec.hom_inv_id).app _ ≪≫
      restrictFunctorId.app _

end Motivic.Intersection
