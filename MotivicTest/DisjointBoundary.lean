/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.DisjointBoundary

/-! Specified full-boundary trivializations retain every component map. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
universe u v

example {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hc : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    (hd : Pairwise fun i j => Disjoint (a i).opensRange (a j).opensRange)
    (M : X.Modules)
    (e : ∀ i, M.restrict (a i) ≅
      (Scheme.Modules.restrictFunctor (a i)).obj (SheafOfModules.unit X.ringCatSheaf)) :
    ∃ E : M ≅ SheafOfModules.unit X.ringCatSheaf,
      ∀ i, (Scheme.Modules.restrictFunctor (a i)).map E.hom = (e i).hom :=
  Scheme.Modules.InternalHom.exists_iso_of_disjoint_restrictions Y a hc hd M _ e

#print axioms AlgebraicGeometry.Scheme.Modules.InternalHom.exists_iso_of_disjoint_restrictions
