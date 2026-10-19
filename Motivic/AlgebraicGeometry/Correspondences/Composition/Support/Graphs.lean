/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Basic

/-!
# Graph and identity geometry of incidence schemes

A graph generator is transported to a specified structural morphism using
its literal equality over the base. The diagonal generator is therefore
available in `FiniteCorrespondenceGenerator f f`, without a unit-composition
transport in its type.

For these actual diagonal generators, left and right incidence schemes are
isomorphic to the original support scheme. The isomorphisms identify the
source-target map with the original closed immersion, so the actual image
ideal is unchanged. These are scheme-level unit identities, not unit laws
for an intersection cycle or a category of correspondences.

An integral-source hypothesis is used only to make a single graph into a
geometric generator. There is no assertion that a smooth object is integral;
disconnected identity graph cycles require the separate componentwise API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}

/-- The actual graph generator, transported along its structural equality over the base. -/
noncomputable def graphGeneratorOver (φ : X ⟶ Y) (w : φ ≫ g = f)
    [IsIntegral X] [IsSeparated g] : FiniteCorrespondenceGenerator f g :=
  w ▸ graphGenerator φ g

instance (φ : X ⟶ Y) (w : φ ≫ g = f) [IsIntegral X] [IsSeparated g] :
    IsIso (graphGeneratorOver φ w).projection := by
  subst f
  exact inferInstanceAs (IsIso (correspondenceProjection (φ ≫ g) g
    (correspondenceGraphIdeal φ g)))

/-- The two graph projections are related by the original morphism. -/
@[reassoc]
theorem graphGeneratorOver_projection_target (φ : X ⟶ Y) (w : φ ≫ g = f)
    [IsIntegral X] [IsSeparated g] :
    (graphGeneratorOver φ w).projection ≫ φ = (graphGeneratorOver φ w).targetProjection := by
  subst f
  have : IsIso (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  apply (cancel_epi (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g).toImage).mp
  simp [graphGeneratorOver, graphGenerator, FiniteCorrespondenceGenerator.projection,
    FiniteCorrespondenceGenerator.targetProjection, FiniteCorrespondenceGenerator.inclusion,
    correspondenceGraphIdeal,
    correspondenceProjection]

/-- The actual diagonal generator on an integral scheme over a separated base morphism. -/
noncomputable def identityGenerator (f : X ⟶ S) [IsIntegral X] [IsSeparated f] :
    FiniteCorrespondenceGenerator f f :=
  graphGeneratorOver (𝟙 X) (Category.id_comp f)

instance [IsIntegral X] [IsSeparated f] : IsIso (identityGenerator f).projection :=
  inferInstanceAs (IsIso (graphGeneratorOver (𝟙 X) (Category.id_comp f)).projection)

/-- The two diagonal projections agree as actual scheme morphisms. -/
@[reassoc (attr := simp)]
theorem identityGenerator_targetProjection [IsIntegral X] [IsSeparated f] :
    (identityGenerator f).targetProjection = (identityGenerator f).projection := by
  simpa only [identityGenerator, Category.comp_id] using
    (graphGeneratorOver_projection_target (𝟙 X) (Category.id_comp f)).symm

namespace FiniteCorrespondenceGenerator

variable (A : FiniteCorrespondenceGenerator f g)

section RightGraph

variable (ψ : Y ⟶ Z) (w : ψ ≫ h = g)

/-- Incidence with a graph on the right has the original first support as its scheme. -/
noncomputable def rightGraphIncidenceIso [IsIntegral Y] [IsSeparated h] :
    A.incidence (graphGeneratorOver ψ w) ≅ A.scheme :=
  asIso (A.incidenceFst (graphGeneratorOver ψ w))

/-- The source-target map obtained by composing the target projection with a morphism. -/
noncomputable def graphPostcompositionMap : A.scheme ⟶ pullback f h :=
  pullback.lift A.projection (A.targetProjection ≫ ψ) (by
    rw [Category.assoc, w]
    exact A.projection_base)

@[reassoc (attr := simp)]
theorem graphPostcompositionMap_fst :
    A.graphPostcompositionMap ψ w ≫ pullback.fst f h = A.projection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphPostcompositionMap_snd :
    A.graphPostcompositionMap ψ w ≫ pullback.snd f h = A.targetProjection ≫ ψ :=
  pullback.lift_snd _ _ _

instance [IsSeparated h] : IsFinite (A.graphPostcompositionMap ψ w) := by
  have : IsFinite (A.graphPostcompositionMap ψ w ≫ pullback.fst f h) := by
    simpa using (inferInstance : IsFinite A.projection)
  exact IsFinite.of_comp (A.graphPostcompositionMap ψ w) (pullback.fst f h)

/-- The graph-incidence isomorphism identifies the source-target map with postcomposition. -/
theorem incidenceMap_graph_right [IsIntegral Y] [IsSeparated h] :
    A.incidenceMap (graphGeneratorOver ψ w) =
      (A.rightGraphIncidenceIso ψ w).hom ≫ A.graphPostcompositionMap ψ w := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc, graphPostcompositionMap_fst]
    rfl
  · simp only [incidenceMap_snd, Category.assoc, graphPostcompositionMap_snd]
    change A.incidenceSnd (graphGeneratorOver ψ w) ≫
        (graphGeneratorOver ψ w).targetProjection =
      A.incidenceFst (graphGeneratorOver ψ w) ≫ A.targetProjection ≫ ψ
    rw [← graphGeneratorOver_projection_target, ← Category.assoc,
      ← A.incidence_condition, Category.assoc]

/-- The graph-incidence image is literally the image of the postcomposed support map. -/
theorem incidenceImageIdeal_graph_right [IsIntegral Y] [IsSeparated h] :
    A.incidenceImageIdeal (graphGeneratorOver ψ w) = (A.graphPostcompositionMap ψ w).ker := by
  rw [incidenceImageIdeal, A.incidenceMap_graph_right, Scheme.Hom.ker_comp_of_isIso]

end RightGraph

section RightIdentity

variable [IsIntegral Y] [IsSeparated g]

/-- Pulling back the actual diagonal support on the right recovers the original support. -/
noncomputable def rightIdentityIncidenceIso : A.incidence (identityGenerator g) ≅ A.scheme :=
  asIso (A.incidenceFst (identityGenerator g))

@[reassoc (attr := simp)]
theorem rightIdentityIncidenceIso_hom_source :
    (A.rightIdentityIncidenceIso).hom ≫ A.projection =
      A.incidenceSource (identityGenerator g) := rfl

/-- The right diagonal incidence projection is the original closed immersion under this iso. -/
theorem incidenceMap_identity_right :
    A.incidenceMap (identityGenerator g) =
      (A.rightIdentityIncidenceIso).hom ≫ A.inclusion := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc]
    rfl
  · simp only [incidenceMap_snd, Category.assoc]
    change A.incidenceSnd (identityGenerator g) ≫ (identityGenerator g).targetProjection =
      A.incidenceFst (identityGenerator g) ≫ A.targetProjection
    rw [identityGenerator_targetProjection, A.incidence_condition]

/-- The scheme-theoretic image of right diagonal incidence is the original ideal sheaf. -/
@[simp]
theorem incidenceImageIdeal_identity_right :
    A.incidenceImageIdeal (identityGenerator g) = A.val := by
  rw [incidenceImageIdeal, A.incidenceMap_identity_right,
    Scheme.Hom.ker_comp_of_isIso]
  exact A.val.ker_subschemeι

end RightIdentity

section LeftIdentity

variable [IsIntegral X] [IsSeparated f]

/-- Pulling back the actual diagonal support on the left recovers the original support. -/
noncomputable def leftIdentityIncidenceIso : (identityGenerator f).incidence A ≅ A.scheme := by
  have : IsIso (identityGenerator f).targetProjection := by
    rw [identityGenerator_targetProjection]
    infer_instance
  exact asIso ((identityGenerator f).incidenceSnd A)

@[reassoc (attr := simp)]
theorem leftIdentityIncidenceIso_hom_target :
    (A.leftIdentityIncidenceIso).hom ≫ A.targetProjection =
      (identityGenerator f).incidenceTarget A := rfl

/-- The left diagonal incidence projection is the original closed immersion under this iso. -/
theorem incidenceMap_identity_left :
    (identityGenerator f).incidenceMap A =
      (A.leftIdentityIncidenceIso).hom ≫ A.inclusion := by
  apply pullback.hom_ext
  · simp only [incidenceMap_fst, Category.assoc]
    change (identityGenerator f).incidenceFst A ≫ (identityGenerator f).projection =
      (identityGenerator f).incidenceSnd A ≫ A.projection
    rw [← identityGenerator_targetProjection, incidence_condition]
  · simp only [incidenceMap_snd, Category.assoc]
    rfl

/-- The scheme-theoretic image of left diagonal incidence is the original ideal sheaf. -/
@[simp]
theorem incidenceImageIdeal_identity_left :
    (identityGenerator f).incidenceImageIdeal A = A.val := by
  rw [incidenceImageIdeal, A.incidenceMap_identity_left,
    Scheme.Hom.ker_comp_of_isIso]
  exact A.val.ker_subschemeι

end LeftIdentity

end FiniteCorrespondenceGenerator

end Motivic
