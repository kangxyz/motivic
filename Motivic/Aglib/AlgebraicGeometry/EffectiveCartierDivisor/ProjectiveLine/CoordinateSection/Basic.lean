/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve
/-! # The actual coordinate graph divisor on the relative projective line

The graph has its original kernel ideal. Rank one follows from the original
smooth affine chart near its range, not an assumed line-bundle structure.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]

/-- Literal graph of the specified coordinate in the projective compactification. -/
def coordinateSection (a : R) : Spec (.of R) ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) ≫ chart R ⟨0⟩

@[reassoc (attr := simp)]
lemma coordinateSection_toSpec (a : R) :
    coordinateSection R a ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) = 𝟙 _ := by
  rw [coordinateSection, Category.assoc, chart_toSpec, ← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 _ := by
    ext x
    simp
  rw [h, Spec.map_id]

instance coordinateSection_isClosedImmersion (a : R) :
    IsClosedImmersion (coordinateSection R a) := by
  have : IsClosedImmersion
      (coordinateSection R a ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
    rw [coordinateSection_toSpec]
    infer_instance
  exact IsClosedImmersion.of_comp _ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))

lemma coordinateOpen_smooth_one (i : ULift.{u} (Fin 2)) :
    SmoothOfRelativeDimension 1
      ((ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) i).ι ≫
        ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  let U := ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) i
  let e := IsOpenImmersion.isoOfRangeEq (chart R i) U.ι (by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun W : (ProjectiveSpace R (ULift.{u} (Fin 2))).Opens =>
      (W : Set (ProjectiveSpace R (ULift.{u} (Fin 2))))) (chart_opensRange R i))
  have he : e.hom ≫ U.ι = chart R i := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.hom]
  rw [← Category.assoc, he, chart_toSpec]
  exact Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

lemma coordinateSection_range (a : R) :
    Set.range (coordinateSection R a) ⊆
      ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) ⟨0⟩ := by
  rintro _ ⟨x, rfl⟩
  rw [← chart_opensRange]
  exact ⟨_, rfl⟩

/-- The entire original kernel ideal of the graph is invertible. -/
lemma coordinateSection_ideal_rankOne (a : R) :
    IsLocallyRankOne (ProjectiveSpace R (ULift.{u} (Fin 2)))
      (Scheme.Hom.idealModule (coordinateSection R a)) := by
  have := coordinateOpen_smooth_one R ⟨0⟩
  exact Scheme.Hom.section_idealModule_isLocallyRankOne
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (coordinateSection R a)
    (coordinateSection_toSpec R a) _ (coordinateSection_range R a)

/-- Original graph ideal line bundle, with no change of its zero scheme. -/
def coordinateIdealLineBundle (a : R) :
    LineBundle (ProjectiveSpace R (ULift.{u} (Fin 2))) :=
  ⟨Scheme.Hom.idealModule (coordinateSection R a), coordinateSection_ideal_rankOne R a⟩
end AlgebraicGeometry.RelativeProjectiveLine
