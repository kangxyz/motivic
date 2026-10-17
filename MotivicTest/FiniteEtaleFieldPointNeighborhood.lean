/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldPointNeighborhood
public import Lean.Util.CollectAxioms

/-! Actual field-valued neighborhood colimit computes the genuine inverse image. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Motivic
open FiniteEtaleSite
universe u
namespace MotivicTest.FiniteEtaleFieldPointNeighborhood
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

/-- Direct consumer retaining the original inverse-image sheaf and literal neighborhood diagram. -/
def actual_neighborhood_inverse_image
    (G : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    colimit ((Functor.Elements.π
      (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ T ⋙
        coyoneda.obj (op (Over.mk (q ≫ b))))).op ⋙ G.obj) ≅
      ((inverseImage b).obj G).obj.obj (op (fieldObject K q)) :=
  fieldNeighborhoodInverseImageIso b K q G

open Lean in
run_cmd do
  for name in #[``actual_neighborhood_inverse_image, ``fieldPointLiftEquiv,
      ``relativeFieldPointFiberEquiv_naturality, ``pointElementsToNeighborhood_initial,
      ``fieldNeighborhoodFiberIso, ``fieldNeighborhoodInverseImageIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field-valued neighborhood / inverse image: standard foundations only."

end MotivicTest.FiniteEtaleFieldPointNeighborhood
