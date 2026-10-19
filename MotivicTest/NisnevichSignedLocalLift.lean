/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.SignedLocalLift

/-!
# Signed local Nisnevich correspondence lifting consumers

No effectivity, connectedness, or perfect-field hypothesis is imposed.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.NisnevichSignedLocalLift

variable {k : Type u} [Field k] {X Y V : SmoothSite (Spec (.of k))}
  (q : V ⟶ Y) [Etale q.left]
  (hq : ∀ y : Y.left, ∃ v : V.left,
    q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left)

example (α : Cor.mk X ⟶ Cor.mk Y) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ α :=
  FiniteCorrespondence.exists_nisnevich_graph_factorization k α q hq x

example (A B : FiniteCorrespondenceGenerator X.hom Y.hom) (n : ℤ) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q =
        (Cor.graphFunctor k).map g ≫ (n • A.cycle - B.cycle) :=
  FiniteCorrespondence.exists_nisnevich_graph_factorization k (n • A.cycle - B.cycle) q hq x

end MotivicTest.NisnevichSignedLocalLift
