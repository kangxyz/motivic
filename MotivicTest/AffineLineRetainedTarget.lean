/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.AffineLineRetainedTarget

/-! The actual overlap, not its projection to U, is the retained target. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y Z T : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (U : (Spec (.of (Polynomial k))).Opens)
    (z : Z ⟶ Spec (.of (Polynomial k))) (s : Z ⟶ Y)
    (H : IsPullback s (𝟙 _) p z)
    (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ)
    (g : T ⟶ compactification k p)
    (hg : Set.range g ⊆
      (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ inclusion k p))ᶜ) :
    ∃ t : T ⟶ pullback U.ι p, t ≫ retainedInclusion k p U = g :=
  ⟨liftToRetained k p U z s H hz g hg, liftToRetained_fac k p U z s H hz g hg⟩
#print axioms AlgebraicGeometry.Scheme.AffineLineEtaleCompactification.liftToRetained_fac
