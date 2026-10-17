/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.GraphBoundarySections

/-! # Actual graph pairs: full-boundary values and original open h-relation -/

@[expose] public section
noncomputable section
set_option linter.hashCommand false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.CoherentGraph
attribute [local instance] Abelian.hasFiniteBiproducts

universe u

example
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    (h : Γ(U, ⊤)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
      ∀ σ : Γ((Modules.pushforward k).obj ((Modules.pushforward (i ≫ j)).obj
          ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
            ((Modules.pullback (i ≫ j)).obj O))), ⊤),
      ∃ s₀ s₁ : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), ⊤),
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app ⊤ s₀ = σ ∧
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app ⊤ s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward (i ≫ j)).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).map
              (boundaryScalar j i h)))).app ⊤ σ) ∧
        (openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app ⊤ s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward j).map
            (openTwistScalar j L h))).app ⊤
              ((openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app ⊤ s₀)) :=
  exists_prescribed_numerator_denominator R ι n e k j i h

-- Direct original-map consumer: every section of this twisted graph
-- obeys the h-relation on U, independently of the boundary lifting step.
example {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (L : C.Modules) (h : Γ(U, ⊤)) (g : GraphExtension j h) :
    (Modules.restrictFunctor j).map
        ((moduleTensorLeftFunctor C L).map (g.inclusion ≫ biprod.fst)) =
      (Modules.restrictFunctor j).map
        ((moduleTensorLeftFunctor C L).map (g.inclusion ≫ biprod.snd)) ≫
          openTwistScalar j L h :=
  twisted_graph_relation_on_open j L h g

#print axioms exists_prescribed_numerator_denominator
#print axioms twisted_graph_relation_on_open
#print axioms boundaryGraphRatio_eq_boundaryScalar
#print axioms extendGraph
