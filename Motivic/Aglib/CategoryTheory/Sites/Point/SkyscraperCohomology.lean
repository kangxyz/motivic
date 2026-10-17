/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Motivic.Cohomology.SheafCohomology

/-!
# Ordinary cohomological acyclicity of a point skyscraper

The actual skyscraper functor of a site point is exact for abelian groups:
its maps on sections are products of the original coefficient maps. The
point adjunction therefore identifies Ext into a skyscraper with Ext from
the fiber of the actual free section-representing sheaf. That fiber is
projective, so the positive ordinary cohomology groups vanish.

This is one ordinary-sheaf ingredient for a pointwise acyclic envelope.
It neither constructs henselian points on a smooth site nor equips an
envelope with transfers, and does not assert acyclicity of transfer injectives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe e e' w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : Point.{max v w} J) [HasSheafify J AddCommGrpCat.{max v w}]

instance skyscraperSheafFunctor_additive :
    (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{max v w})).Additive :=
  Functor.additive_of_preserves_binary_products _

instance sheafFiber_additive :
    (Φ.sheafFiber (A := AddCommGrpCat.{max v w})).Additive :=
  Functor.additive_of_preserves_binary_products _

omit [HasSheafify J AddCommGrpCat.{max v w}] in
/-- A skyscraper coefficient epimorphism is an epimorphism on every section group. -/
theorem epi_skyscraperSheaf_map_app {M N : AddCommGrpCat.{max v w}}
    (f : M ⟶ N) [Epi f] (X : C) :
    Epi ((Φ.skyscraperSheafFunctor.map f).hom.app (op X)) := by
  have : Epi (Discrete.natTrans
      (F := Discrete.functor (fun _ : Φ.fiber.obj X ↦ M))
      (G := Discrete.functor (fun _ : Φ.fiber.obj X ↦ N)) (fun _ ↦ f)) := by
    rw [NatTrans.epi_iff_epi_app]
    intro i
    exact inferInstanceAs (Epi f)
  change Epi (lim.map (Discrete.natTrans
    (F := Discrete.functor (fun _ : Φ.fiber.obj X ↦ M))
    (G := Discrete.functor (fun _ : Φ.fiber.obj X ↦ N)) (fun _ ↦ f)))
  infer_instance

instance skyscraperSheafFunctor_preservesEpimorphisms :
    (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{max v w})).PreservesEpimorphisms where
  preserves f _ := by
    have : Epi ((Φ.skyscraperSheafFunctor.map f).hom) := by
      rw [NatTrans.epi_iff_epi_app]
      intro X
      exact Φ.epi_skyscraperSheaf_map_app f X.unop
    exact (sheafToPresheaf J AddCommGrpCat).epi_of_epi_map this

instance skyscraperSheafFunctor_preservesHomology :
    (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{max v w})).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance skyscraperSheafFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{max v w})) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- The fiber of the actual free section-representing sheaf is projective.
Lifts are transported through the point adjunction and section representation. -/
theorem projective_sheafFiber_freeAbelianSheaf (X : C) :
    Projective (Φ.sheafFiber.obj (Motivic.Hypercohomology.freeAbelianSheaf J X)) where
  factors {M N} f g _ := by
    let S := Motivic.Hypercohomology.freeAbelianSheaf J X
    let adj := Φ.skyscraperSheafAdjunction (A := AddCommGrpCat.{max v w})
    have := Φ.epi_skyscraperSheaf_map_app g X
    obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective
      ((Φ.skyscraperSheafFunctor.map g).hom.app (op X))).mp inferInstance
      (Motivic.Hypercohomology.sectionsEquiv J X (Φ.skyscraperSheaf N)
        (adj.homEquiv S N f))
    refine ⟨(adj.homEquiv S M).symm
      ((Motivic.Hypercohomology.sectionsEquiv J X (Φ.skyscraperSheaf M)).symm x), ?_⟩
    apply (adj.homEquiv S N).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply (Motivic.Hypercohomology.sectionsEquiv J X (Φ.skyscraperSheaf N)).injective
    rw [Motivic.Hypercohomology.sectionsEquiv_naturality, Equiv.apply_symm_apply]
    exact hx

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max v w})]
  [HasExt.{e'} AddCommGrpCat.{max v w}]

/-- Ordinary cohomology with skyscraper coefficients is the actual Ext group
from the projective fiber of its section-representing source. -/
def skyscraperCohomologyComparison (M : AddCommGrpCat.{max v w}) (n : ℕ) (X : C) :
    Motivic.SheafCohomology.H J (Φ.skyscraperSheaf M) n X ≃+
      Ext (Φ.sheafFiber.obj (Motivic.Hypercohomology.freeAbelianSheaf J X)) M n :=
  Φ.skyscraperSheafAdjunction.extEquiv.symm

/-- The comparison uses the original restriction map and the fiber of the
original free-source map. -/
theorem skyscraperCohomologyComparison_restriction
    (M : AddCommGrpCat.{max v w}) (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (x : Motivic.SheafCohomology.H J (Φ.skyscraperSheaf M) n Y) :
    Φ.skyscraperCohomologyComparison M n X
        ((Motivic.SheafCohomology.presheaf J (Φ.skyscraperSheaf M) n).map f.op x) =
      (Ext.mk₀ (Φ.sheafFiber.map
        ((Motivic.Hypercohomology.freeAbelianSheafFunctor J).map f))).comp
          (Φ.skyscraperCohomologyComparison M n Y x) (zero_add n) :=
  Φ.skyscraperSheafAdjunction.extEquiv_symm_naturality_left₀ _ x

/-- The comparison respects the skyscraper map induced by the original
coefficient homomorphism. -/
theorem skyscraperCohomologyComparison_coefficient
    {M N : AddCommGrpCat.{max v w}} (f : M ⟶ N) (n : ℕ) (X : C)
    (x : Motivic.SheafCohomology.H J (Φ.skyscraperSheaf M) n X) :
    Φ.skyscraperCohomologyComparison N n X
        (((Motivic.SheafCohomology.presheafFunctor J n).map
          (Φ.skyscraperSheafFunctor.map f)).app (op X) x) =
      (Φ.skyscraperCohomologyComparison M n X x).comp (Ext.mk₀ f) (add_zero n) :=
  Φ.skyscraperSheafAdjunction.extEquiv_symm_naturality_right₀ x f

/-- Every positive ordinary cohomology class of a point skyscraper vanishes. -/
theorem skyscraper_cohomology_eq_zero (M : AddCommGrpCat.{max v w}) (n : ℕ) (X : C)
    (x : Motivic.SheafCohomology.H J (Φ.skyscraperSheaf M) (n + 1) X) : x = 0 := by
  have := Φ.projective_sheafFiber_freeAbelianSheaf X
  apply (Φ.skyscraperCohomologyComparison M (n + 1) X).injective
  rw [map_zero]
  exact Ext.eq_zero_of_projective _

end CategoryTheory.GrothendieckTopology.Point
