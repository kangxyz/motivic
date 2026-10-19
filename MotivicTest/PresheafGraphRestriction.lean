/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.GraphRestriction
public import Motivic.Aglib.Algebra.Homology.SingularComplex.Presheaf
public import Lean.Util.CollectAxioms

/-!
# Ordinary restriction of actual presheaves with transfers

These consumers use the proved graph functor on every smooth object over an
arbitrary field. They check graph restriction, ordinary contravariant
composition, faithful additive forgetfulness, actual-cycle representables,
and compatibility with the pre-existing singular-presheaf construction.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic
open  _root_.Motivic.PresheafWithTransfers

universe v u

namespace MotivicTest.PresheafGraphRestriction

variable {k : Type u} [Field k]

local instance (X : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance (X : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

example : (toPresheaf.{v} k).Additive := inferInstance
example : (toPresheaf.{v} k).Faithful := inferInstance

/-- Ordinary pullback is literally transfer along the actual componentwise graph cycle. -/
theorem actualGraphAction (P : PresheafWithTransfers.{v} k)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    ((toPresheaf k).obj P).map f.op =
      transfer P (X := Cor.mk X) (Y := Cor.mk Y)
        (componentGraphCycleOver f.left (MorphismProperty.Over.w f)) := rfl

/-- The ordinary restriction obeys contravariant composition on all smooth objects. -/
theorem restrictionComp (P : PresheafWithTransfers.{v} k)
    {X Y Z : SmoothSite (Spec (.of k))} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((toPresheaf k).obj P).map (f ≫ g).op =
      ((toPresheaf k).obj P).map g.op ≫ ((toPresheaf k).obj P).map f.op :=
  ((toPresheaf k).obj P).map_comp g.op f.op

/-- The representable underlying presheaf is still valued in the actual cycle groups. -/
theorem actualRepresentableValue (X Y : SmoothSite (Spec (.of k))) :
    ((toPresheaf k).obj ((representable k).obj (Cor.mk X))).obj (op Y) =
      AddCommGrpCat.of (FiniteCorrespondence Y.hom X.hom) := rfl

/-- The existing ordinary singular-chain construction accepts graph-restricted transfers. -/
def ordinarySingularComplex
    [HasBinaryProducts (SmoothSite (Spec (.of k)))]
    (Δ : CosimplicialObject (SmoothSite (Spec (.of k))))
    (P : PresheafWithTransfers.{v} k) :
    ChainComplex ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  _root_.CategoryTheory.SingularComplex.presheafObj Δ ((toPresheaf k).obj P)

open Lean in
run_cmd do
  let dependencies ← collectAxioms ``Motivic.PresheafWithTransfers.toPresheaf
  for dependency in dependencies do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwError "Graph restriction depends on unsupported assumption {dependency}"
  logInfo "Graph restriction uses only standard Lean logical foundations."

end MotivicTest.PresheafGraphRestriction
