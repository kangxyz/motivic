/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichGeneratorLift
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor

/-!
# A literal finite-support lift gives an actual correspondence factorization

The source map need not be flat or étale. All geometric lifting assumptions
are carried by the supplied map of the actual support pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.NisnevichGeneratorLift

variable {k : Type u} [Field k] {X Y U V : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (g : U ⟶ X) (q : V ⟶ Y)
  (b : pullback A.projection g.left ⟶ V.left)
  (hb : b ≫ q.left = pullback.fst A.projection g.left ≫ A.targetProjection)

local instance (W : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj W.left) :=
  inferInstanceAs (IsNoetherian W.left)

local instance (W : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj W.left) :=
  inferInstanceAs (IsReduced W.left)

example :
    ∃ β : FiniteCorrespondence U.hom V.hom,
      FiniteCorrespondence.incidenceTorPairing k
        (X := U) (Y := V) (Z := Y) β
        (componentGraphCycleOver q.left (MorphismProperty.Over.w q)) =
      FiniteCorrespondence.incidenceTorPairing k
        (X := U) (Y := X) (Z := Y)
        (componentGraphCycleOver g.left (MorphismProperty.Over.w g)) A.cycle :=
  A.exists_graph_factorization_of_support_lift k g q b hb

example :
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ A.cycle :=
  A.exists_graph_factorization_of_support_lift k g q b hb

end MotivicTest.NisnevichGeneratorLift
