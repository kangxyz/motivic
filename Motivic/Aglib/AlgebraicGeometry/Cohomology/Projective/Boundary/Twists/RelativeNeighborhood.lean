/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroNeighborhoodBoundary
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Principal
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.RelativeCurve.ActualConstantCurveMap
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.FiniteGraphSections

/-! # Uniform twists on the whole relative zero-neighborhood boundary

One principal base shrink trivializes all powers on the original entire finite
boundary. The chosen units then pull to the actual full boundary product with
any unchanged affine source over that principal open. The relative twists are
identified using the native projective twisting base-change isomorphism.
No field hypothesis, monic refinement, or further source shrink is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.RelativeProjectiveLine

variable (R : Type u) [CommRing R]
  (V : (Spec (.of (Polynomial R))).Opens)

/-- The unchanged full prescribed boundary's structural morphism. -/
abbrev fullBoundaryStructure :=
  fullNeighborhoodBoundaryMap R V ≫ toSpec R (ULift.{u} (Fin 2))

/-- Only the base is shrunk; the full boundary is taken over that same principal open. -/
abbrev fullBoundaryPrincipalOpen (r : R) :=
  fullBoundaryStructure R V ⁻¹ᵁ PrimeSpectrum.basicOpen r

/-- A single principal base neighborhood works for every nonnegative twist of the
whole actual complement-plus-zero boundary. -/
theorem exists_fullBoundary_principal_positiveTwist_unitIso
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V)
    (s : Spec (.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      Nonempty ((n : ℕ) →
        (Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
          fullNeighborhoodBoundaryMap R V)).obj
          (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
          SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf) := by
  let := fullNeighborhoodBoundary_finite R V hV
  exact Scheme.CoherentGraph.exists_principal_positiveTwist_unitIso R _
    (fullNeighborhoodBoundaryMap R V) s

variable (r : R) {A : Type u} [CommRing A]
  (b : Spec (.of A) ⟶ (Scheme.Opens.toScheme (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)))

/-- The original affine source map, including its specified factorization through D(r). -/
abbrev sourceMap := b ≫ (Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r))

/-- The original full boundary product; no open subset of the affine source is substituted. -/
abbrev fullBoundarySource := pullback (sourceMap R r b) (fullBoundaryStructure R V)

/-- The actual full-source projection lands in the principal boundary neighborhood. -/
theorem boundaryProjection_range :
    Set.range (pullback.snd (sourceMap R r b) (fullBoundaryStructure R V)) ⊆
      Set.range (fullBoundaryPrincipalOpen R V r).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change (fullBoundaryStructure R V)
    (pullback.snd (sourceMap R r b) (fullBoundaryStructure R V) x) ∈
      (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens)
  have h := congrArg (fun f ↦ f x)
    (pullback.condition (f := sourceMap R r b) (g := fullBoundaryStructure R V))
  change (sourceMap R r b)
      (pullback.fst (sourceMap R r b) (fullBoundaryStructure R V) x) =
      (fullBoundaryStructure R V)
        (pullback.snd (sourceMap R r b) (fullBoundaryStructure R V) x) at h
  rw [← h]
  exact (b (pullback.fst (sourceMap R r b) (fullBoundaryStructure R V) x)).property

/-- Factor the unchanged full boundary projection through the one chosen base shrink. -/
def boundaryProjectionToPrincipal :
    fullBoundarySource R V r b ⟶ (fullBoundaryPrincipalOpen R V r).toScheme :=
  IsOpenImmersion.lift (fullBoundaryPrincipalOpen R V r).ι
    (pullback.snd (sourceMap R r b) (fullBoundaryStructure R V))
    (boundaryProjection_range R V r b)

@[reassoc (attr := simp)]
theorem boundaryProjectionToPrincipal_ι :
    boundaryProjectionToPrincipal R V r b ≫ (fullBoundaryPrincipalOpen R V r).ι =
      pullback.snd (sourceMap R r b) (fullBoundaryStructure R V) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual relative projective map of the unchanged full boundary product. -/
abbrev boundaryRelativeMap : fullBoundarySource R V r b ⟶
    ProjectiveSpace A (ULift.{u} (Fin 2)) :=
  Scheme.ConstantCurve.actualToProjectiveSpace (sourceMap R r b) _
    (fullNeighborhoodBoundaryMap R V)

/-- Pull the same uniform units to the native relative O(n), with no source shrink. -/
def fullBoundaryRelativeTwistIso
    (e : (n : ℕ) →
      (Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
        fullNeighborhoodBoundaryMap R V)).obj
        (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf)
    (n : ℕ) :
    (Modules.pullback (boundaryRelativeMap R V r b)).obj
      (twistingSheaf A (ULift.{u} (Fin 2)) (n : ℤ)) ≅
      SheafOfModules.unit (fullBoundarySource R V r b).ringCatSheaf :=
  Scheme.ConstantCurve.actualOriginalTwistIso (sourceMap R r b) _
      (fullNeighborhoodBoundaryMap R V) (n : ℤ) ≪≫
    (Modules.pullbackComp (pullback.snd (sourceMap R r b) (fullBoundaryStructure R V))
      (fullNeighborhoodBoundaryMap R V)).app _ ≪≫
    (Modules.pullbackCongr (by
      simp only [← Category.assoc, boundaryProjectionToPrincipal_ι])).app _ ≪≫
    (Modules.pullbackComp (boundaryProjectionToPrincipal R V r b)
      ((fullBoundaryPrincipalOpen R V r).ι ≫ fullNeighborhoodBoundaryMap R V)).symm.app _ ≪≫
    (Modules.pullback (boundaryProjectionToPrincipal R V r b)).mapIso (e n) ≪≫
    pullbackUnitIso (boundaryProjectionToPrincipal R V r b)

variable
  (e : (n : ℕ) →
    (Modules.pullback ((fullBoundaryPrincipalOpen R V r).ι ≫
      fullNeighborhoodBoundaryMap R V)).obj
      (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
      SheafOfModules.unit (fullBoundaryPrincipalOpen R V r).toScheme.ringCatSheaf)
  {C : Scheme.{u}} (a : C ⟶ ProjectiveSpace A (ULift.{u} (Fin 2)))
  (z : fullBoundarySource R V r b ⟶ C) (ha : z ≫ a = boundaryRelativeMap R V r b)

/-- The exact tensor coefficient sheaf used by the section producer, on the
unchanged whole boundary product. -/
abbrev fullBoundaryRelativeCoefficient (n : ℕ) :=
  (moduleTensorLeftFunctor (fullBoundarySource R V r b)
    ((Modules.pullback z).obj ((Modules.pullback a).obj
      (twistingSheaf A (ULift.{u} (Fin 2)) (n : ℤ))))).obj
    ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))

/-- The uniform units trivialize the original relative boundary coefficient,
not a replacement coefficient or a smaller source. -/
def fullBoundaryRelativeCoefficientIso (n : ℕ) :
    fullBoundaryRelativeCoefficient R V r b a z n ≅
      SheafOfModules.unit (fullBoundarySource R V r b).ringCatSheaf :=
  Scheme.CoherentGraph.boundaryTwistCoefficientIso a z
      (twistingSheaf A (ULift.{u} (Fin 2)) (n : ℤ)) ≪≫
    (Modules.pullbackCongr ha).app _ ≪≫ fullBoundaryRelativeTwistIso R V r b e n

/-- The actual prescribed unit section in the original relative boundary coefficient. -/
def fullBoundaryRelativeCoefficientUnitSection (n : ℕ) :
    Γ(fullBoundaryRelativeCoefficient R V r b a z n, ⊤) :=
  (unitHomGlobalSectionsEquiv (fullBoundarySource R V r b)
    (fullBoundaryRelativeCoefficient R V r b a z n))
    (fullBoundaryRelativeCoefficientIso R V r b e a z ha n).inv

/-- This unit is a generating section on the entire original source product. -/
theorem fullBoundaryRelativeCoefficientUnitSection_isIso (n : ℕ) :
    IsIso ((unitHomGlobalSectionsEquiv (fullBoundarySource R V r b)
      (fullBoundaryRelativeCoefficient R V r b a z n)).symm
        (fullBoundaryRelativeCoefficientUnitSection R V r b e a z ha n)) := by
  rw [fullBoundaryRelativeCoefficientUnitSection, Equiv.symm_apply_apply]
  infer_instance

end AlgebraicGeometry.RelativeProjectiveLine
