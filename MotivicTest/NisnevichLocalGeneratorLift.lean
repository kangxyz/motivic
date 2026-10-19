/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.LocalGeneratorLift

/-! # An actual pointed local lift of a finite-correspondence generator -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace MotivicTest.NisnevichLocalGeneratorLift

variable {k : Type u} [Field k] {X Y V : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom) (q : V ⟶ Y) [Etale q.left]
  (hq : ∀ y : Y.left, ∃ v : V.left, q.left v = y ∧ IsIso (q.left.residueFieldMap v))
  (x : X.left)

example :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ A.cycle :=
  A.exists_nisnevich_graph_factorization k q hq x

end MotivicTest.NisnevichLocalGeneratorLift
