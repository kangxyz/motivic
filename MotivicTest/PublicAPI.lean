/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic

/-! # Public import and object-identity checks

This consumer uses only the package entry and keeps the original ordinary
cohomology group, rather than replacing it with transfer-category Ext.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe w u

namespace MotivicTest.PublicAPI

variable (k : Type u) [Field k]

example : Category (Motivic.Cor k) := inferInstance
example : Preadditive (Motivic.Cor k) := inferInstance

variable [HasExt.{w}
  (Sheaf (Motivic.SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The exported transfer structure acts on the original ordinary group. -/
example (F : Motivic.SheafWithTransfers.{u + 1} k) (n : ℕ) (X : Motivic.Cor k) :
    (Motivic.SheafCohomology.withTransfers k F n).sections X =
      Motivic.SheafCohomology.H.{w, u + 1, u, u + 1}
        (Motivic.SmoothSite.nisnevichTopology (Spec (.of k)))
        ((Motivic.SheafWithTransfers.toSheaf k).obj F) n X.toSmoothSite := rfl

end MotivicTest.PublicAPI
