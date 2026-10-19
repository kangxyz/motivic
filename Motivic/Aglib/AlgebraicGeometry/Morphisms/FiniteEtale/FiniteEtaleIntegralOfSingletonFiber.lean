/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.Topology.Connected.Clopen

/-!
# Integrality from one singleton full fiber of a finite open morphism

Every nonempty clopen component maps onto the connected base. A nonempty
singleton entire fiber therefore forces all components to coincide. The
source stalk-domain hypothesis supplies reducedness and disjoint components;
no selected branch is substituted for the full fiber.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A finite open morphism with a nonempty singleton full fiber has integral
source if the source is Noetherian with domain stalks and the base is connected. -/
theorem isIntegral_of_finite_open_singletonFiber
    {X Y : Scheme.{u}} [IsNoetherian X] [PreconnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [UniversallyOpen f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (x₀ : X) (hf : ∀ x : X, f x = f x₀ → x = x₀) : IsIntegral X := by
  have hsurj (W : Set X) (hW : W ∈ irreducibleComponents X) :
      f '' W = Set.univ := by
    have hcl := isClopen_irreducibleComponent_of_domain_stalks hX hW
    have him : IsClopen (f '' W) := ⟨f.isClosedMap W hcl.1, f.isOpenMap W hcl.2⟩
    exact him.eq_univ (hW.1.1.image f)
  have hcomp : irreducibleComponent x₀ = (Set.univ : Set X) := by
    apply Set.eq_univ_of_forall
    intro x
    let W := irreducibleComponent x
    have hW : W ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hx₀ : f x₀ ∈ f '' W := by rw [hsurj W hW]; trivial
    obtain ⟨x', hx', heq⟩ := hx₀
    have hx₀W : x₀ ∈ W := hf x' heq ▸ hx'
    have he := irreducibleComponents_eq_of_mem_of_domain_stalks hX hW
      (irreducibleComponent_mem_irreducibleComponents x₀) hx₀W mem_irreducibleComponent
    exact he ▸ (mem_irreducibleComponent : x ∈ irreducibleComponent x)
  have hirr : IsIrreducible (irreducibleComponent x₀) := isIrreducible_irreducibleComponent
  rw [hcomp] at hirr
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr hirr
  have : IsReduced X := isReduced_of_domain_stalks X hX
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- Finite étale maps are open, so the full-fiber criterion applies directly. -/
theorem isIntegral_of_finite_etale_singletonFiber
    {X Y : Scheme.{u}} [IsNoetherian X] [PreconnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (x₀ : X) (hf : ∀ x : X, f x = f x₀ → x = x₀) : IsIntegral X :=
  isIntegral_of_finite_open_singletonFiber f hX x₀ hf

end AlgebraicGeometry.Scheme
