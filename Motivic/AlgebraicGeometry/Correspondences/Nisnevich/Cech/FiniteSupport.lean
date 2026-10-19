/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.CommonImage
public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift

/-!
# A common finite image for Čech contraction

A nonempty finite set of correspondence supports has one actual closed image
finite over the source after target postcomposition. Every original support
factors through it. Every actual incidence with a source component graph then
maps to the whole base change of this common support, with both the source and
postcomposed target maps preserved. These constructions do not replace the
incidence scheme by its reduction and make no assumption on its Tor weights.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  {X Y U V : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

namespace FiniteCorrespondence

/-- One actual closed scheme, finite over the source, contains the images of
every selected correspondence support with its literal factor maps. -/
theorem exists_common_finite_image
    (s : Finset (FiniteCorrespondenceGenerator X.hom V.hom)) (hs : s.Nonempty)
    (q : V ⟶ Y) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst X.hom Y.hom) ∧
      ∀ A ∈ s, ∃ r : A.scheme ⟶ C,
        r ≫ j = A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) := by
  apply AlgebraicGeometry.exists_finite_common_closed_image
    (fun A : FiniteCorrespondenceGenerator X.hom V.hom ↦ A.scheme)
    (fun A ↦ A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (pullback.fst X.hom Y.hom) s hs
  intro A _
  rw [FiniteCorrespondenceGenerator.graphPostcompositionMap_fst]
  infer_instance

end FiniteCorrespondence

namespace FiniteCorrespondenceGenerator

variable (A : FiniteCorrespondenceGenerator X.hom V.hom) (q : V ⟶ Y)
  (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) (r : A.scheme ⟶ C)
  (hr : r ≫ j = A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
  (g : U ⟶ X) (E : Set U.left) (hE : E ∈ irreducibleComponents U.left)

/-- The entire graph incidence maps into the actual base change of a common
image support. Its nilpotents and its original multiplicities are untouched. -/
def graphIncidenceToCommonSupport :
    (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
      (MorphismProperty.Over.w g) E hE).incidence A ⟶
    pullback (j ≫ pullback.fst X.hom Y.hom) g.left := by
  let G := componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
    (MorphismProperty.Over.w g) E hE
  refine pullback.lift (G.incidenceSnd A ≫ r) (G.incidenceSource A) ?_
  calc
    _ = G.incidenceSnd A ≫ A.projection := by
      rw [Category.assoc, ← Category.assoc r j, hr, graphPostcompositionMap_fst]
    _ = G.incidenceFst A ≫ G.targetProjection := (G.incidence_condition A).symm
    _ = G.incidenceSource A ≫ g.left := by
      dsimp only [incidenceSource]
      rw [Category.assoc, componentGraphGeneratorOver_projection_target]

@[reassoc (attr := simp)]
theorem graphIncidenceToCommonSupport_fst :
    graphIncidenceToCommonSupport k A q C j r hr g E hE ≫
      pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left =
    (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
      (MorphismProperty.Over.w g) E hE).incidenceSnd A ≫ r :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphIncidenceToCommonSupport_snd :
    graphIncidenceToCommonSupport k A q C j r hr g E hE ≫
      pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left =
    (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
      (MorphismProperty.Over.w g) E hE).incidenceSource A :=
  pullback.lift_snd _ _ _

/-- The common-support factor retains the original postcomposed target map. -/
@[reassoc]
theorem graphIncidenceToCommonSupport_target :
    graphIncidenceToCommonSupport k A q C j r hr g E hE ≫
      pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫ j ≫
        pullback.snd X.hom Y.hom =
    (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
      (MorphismProperty.Over.w g) E hE).incidenceTarget A ≫ q.left := by
  rw [graphIncidenceToCommonSupport_fst_assoc, Category.assoc,
    ← Category.assoc r j, hr, graphPostcompositionMap_snd]

/-- The common-support factor of the whole incidence is finite whenever the
common support is finite over the original source. -/
instance graphIncidenceToCommonSupport_isFinite
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)] :
    IsFinite (graphIncidenceToCommonSupport k A q C j r hr g E hE) := by
  have : IsFinite (graphIncidenceToCommonSupport k A q C j r hr g E hE ≫
      pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left) := by
    rw [graphIncidenceToCommonSupport_snd]
    infer_instance
  exact IsFinite.of_comp _ (pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left)

end FiniteCorrespondenceGenerator

end Motivic
