/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Functor
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual graph functor

These checks use arbitrary smooth-site objects over an arbitrary field, with
no connectedness, integrality, or nonemptiness hypotheses. They retain literal
component graph coefficients and exercise the ordinary categorical functor API.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorrespondenceGraphFunctor
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

/-- Every smooth object is sent to the correspondence-category wrapper. -/
theorem object (X : SmoothSite (Spec (.of k))) :
    (Cor.graphFunctor k).obj X = Cor.mk X := rfl

/-- Morphisms are literal componentwise graph cycles. -/
theorem actualMap (φ : X ⟶ Y) :
    (Cor.graphFunctor k).map φ =
      componentGraphCycleOver φ.left (MorphismProperty.Over.w φ) := rfl

/-- Each source component has multiplicity one in the actual graph. -/
theorem componentCoefficient (φ : X ⟶ Y)
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left) :
    Finsupp.toFun (α := FiniteCorrespondenceGenerator X.hom Y.hom) (M := ℤ)
      ((Cor.graphFunctor k).map φ)
      (componentGraphGeneratorOver φ.left (MorphismProperty.Over.w φ) C hC) = 1 :=
  componentGraphCycleOver_coefficient φ.left (MorphismProperty.Over.w φ) C hC

/-- The categorical identity is preserved without any integrality hypothesis. -/
theorem identity (X : SmoothSite (Spec (.of k))) :
    (Cor.graphFunctor k).map (𝟙 X) = 𝟙 ((Cor.graphFunctor k).obj X) :=
  (Cor.graphFunctor k).map_id X

/-- Composition is preserved by the standard functor API. -/
theorem composition (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (Cor.graphFunctor k).map (φ ≫ ψ) =
      (Cor.graphFunctor k).map φ ≫ (Cor.graphFunctor k).map ψ :=
  (Cor.graphFunctor k).map_comp φ ψ

/-- The preserved composition is specifically the actual incidence Tor pairing. -/
theorem actualComposition (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (componentGraphCycleOver φ.left (MorphismProperty.Over.w φ))
      (componentGraphCycleOver ψ.left (MorphismProperty.Over.w ψ)) =
        componentGraphCycleOver (φ ≫ ψ).left (MorphismProperty.Over.w (φ ≫ ψ)) :=
  ((Cor.graphFunctor k).map_comp φ ψ).symm

/-- Empty sources have the actual zero identity graph. -/
theorem emptyIdentity (X : SmoothSite (Spec (.of k))) [IsEmpty X.left] :
    (Cor.graphFunctor k).map (𝟙 X) = 0 :=
  componentIdentityCycle_eq_zero_of_isEmpty (X := X.left) X.hom

/-- Any graph from an empty smooth source is the zero actual cycle. -/
theorem emptySource (φ : X ⟶ Y) [IsEmpty X.left] :
    (Cor.graphFunctor k).map φ = 0 := by
  change componentGraphCycleOver (X := X.left) φ.left (MorphismProperty.Over.w φ) = 0
  ext A
  exact isEmptyElim (A.projection (Classical.arbitrary A.scheme))

open Lean in
run_cmd do
  for name in #[``Motivic.incidenceTorPairing_componentGraph_comp, ``Motivic.Cor.graphFunctor] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Graph composition and graph functor use only standard Lean logical foundations."

end MotivicTest.CorrespondenceGraphFunctor
