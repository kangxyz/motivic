/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.FiniteSupport
public import Lean.Util.CollectAxioms

/-!
# Common finite supports for arbitrary signed correspondences

A nonzero signed cycle has an actual common closed image. Whole source-graph
incidences factor through its base change without a flatness or reducedness
assumption. The actual coefficient-bearing incidence scheme is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteCorrespondenceGenerator

universe u

namespace MotivicTest.NisnevichCechFiniteSupport

variable {k : Type u} [Field k] {X Y U V : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

example (α : FiniteCorrespondence X.hom V.hom) (hα : α ≠ 0) (q : V ⟶ Y) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst X.hom Y.hom) ∧
      ∀ A ∈ α.support, ∃ r : A.scheme ⟶ C,
        r ≫ j = A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) :=
  FiniteCorrespondence.exists_common_finite_image k α.support
    (Finsupp.support_nonempty_iff.mpr hα) q

example (A : FiniteCorrespondenceGenerator X.hom V.hom) (q : V ⟶ Y)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) (r : A.scheme ⟶ C)
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (hr : r ≫ j = A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (g : U ⟶ X) (E : Set U.left) (hE : E ∈ irreducibleComponents U.left) :
    ∃ a : (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
        (MorphismProperty.Over.w g) E hE).incidence A ⟶
        pullback (j ≫ pullback.fst X.hom Y.hom) g.left,
      IsFinite a ∧
      a ≫ pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left =
        (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
          (MorphismProperty.Over.w g) E hE).incidenceSource A ∧
      a ≫ pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫ j ≫
        pullback.snd X.hom Y.hom =
        (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
          (MorphismProperty.Over.w g) E hE).incidenceTarget A ≫ q.left :=
  ⟨graphIncidenceToCommonSupport k A q C j r hr g E hE, inferInstance,
    graphIncidenceToCommonSupport_snd k A q C j r hr g E hE,
    graphIncidenceToCommonSupport_target k A q C j r hr g E hE⟩

open Lean in
run_cmd do
  for name in #[``FiniteCorrespondence.exists_common_finite_image,
      ``graphIncidenceToCommonSupport_target,
      ``graphIncidenceToCommonSupport_isFinite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichCechFiniteSupport
