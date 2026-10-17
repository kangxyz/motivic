/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteEtaleNeighborhoodIso
public import Lean.Util.CollectAxioms

/-!
# Consumers of the finite étale isomorphism-neighborhood theorem

The endpoint takes singleton-fiber uniqueness and the actual residue-field map,
without imposing reducedness, connectedness, or nonemptiness on the base. The
fiber section is checked against the actual fiber map in both directions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace MotivicTest.FiniteEtaleNeighborhoodIso

example {V Z : Scheme.{u}} (q : V ⟶ Z) [IsFinite q] [Etale q]
    (z : Z) (v : V) (hv : q v = z)
    (hunique : ∀ v' : V, q v' = z → v' = v) (hres : IsIso (q.residueFieldMap v)) :
    ∃ W : Z.Opens, z ∈ W ∧ IsIso (q ∣_ W) :=
  q.exists_isIso_morphismRestrict_of_singleton z v hv hunique hres

example {V Z : Scheme.{u}} (q : V ⟶ Z) [Etale q]
    (v : V) [IsIso (q.residueFieldMap v)]
    (hunique : ∀ v' : V, q v' = q v → v' = v) :
    q.fiberSectionOfResidueFieldIso v ≫ q.fiberToSpecResidueField (q v) = 𝟙 _ ∧
      q.fiberToSpecResidueField (q v) ≫ q.fiberSectionOfResidueFieldIso v = 𝟙 _ :=
  ⟨q.fiberSectionOfResidueFieldIso_fiberToSpecResidueField v,
    q.fiberToSpecResidueField_fiberSectionOfResidueFieldIso v hunique⟩

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (y : Y) (hy : f.finrank y = 1) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) :=
  f.exists_isIso_morphismRestrict_of_finrank_eq_one y hy

example {R : Type u} [CommRing R] {V : Scheme.{u}}
    (q : V ⟶ Spec (.of (R × R))) [IsFinite q] [Etale q]
    (v : V) (hunique : ∀ v' : V, q v' = q v → v' = v)
    (hres : IsIso (q.residueFieldMap v)) :
    ∃ W : (Spec (.of (R × R))).Opens, q v ∈ W ∧ IsIso (q ∣_ W) :=
  q.exists_isIso_morphismRestrict_of_singleton (q v) v rfl hunique hres

open Lean in
run_cmd do
  for name in #[``Scheme.Hom.fiberSectionOfResidueFieldIso,
      ``Scheme.Hom.fiberSectionOfResidueFieldIso_fiberToSpecResidueField,
      ``Scheme.Hom.isOpenImmersion_of_section_of_etale,
      ``Scheme.Hom.isIso_fiberToSpecResidueField_of_singleton,
      ``Scheme.Hom.fiberToSpecResidueField_fiberSectionOfResidueFieldIso,
      ``Scheme.Hom.exists_isIso_morphismRestrict_of_finrank_eq_one,
      ``Scheme.Hom.exists_isIso_morphismRestrict_of_isIso_fiber,
      ``Scheme.Hom.exists_isIso_morphismRestrict_of_singleton] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.FiniteEtaleNeighborhoodIso
