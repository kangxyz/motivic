/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FundamentalClosedSubscheme

/-! # Consumers of actual generic-stalk fundamental cycles -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u v

variable {X Y : Scheme.{u}}

example (x : X) : (IntegralClosedSubscheme.pointClosure x).point = x :=
  IntegralClosedSubscheme.point_pointClosure x

example (I : X.IdealSheafData) : IsReduced I.radical.subscheme := inferInstance

example [IsLocallyNoetherian X] (x : genericPoints X) :
    IsArtinianRing (X.presheaf.stalk x.val) :=
  isArtinianRing_stalk_of_mem_genericPoints x.val x.property

example [IsLocallyNoetherian X] (x : genericPoints X) :
    (genericMultiplicity x : ℕ∞) =
      Module.length (X.presheaf.stalk x.val) (X.presheaf.stalk x.val) :=
  genericMultiplicity_eq_length x

example [IsLocallyNoetherian X] (x : genericPoints X) (M : Type v) [AddCommGroup M]
    [Module (X.presheaf.stalk x.val) M] [Module.Finite (X.presheaf.stalk x.val) M] :
    Module.length (X.presheaf.stalk x.val) M ≠ ⊤ :=
  stalk_module_length_ne_top_of_mem_genericPoints x.val x.property M

example [IsNoetherian X] (x : X) :
    x ∈ (fundamentalPointCycle X).support ↔ x ∈ genericPoints X :=
  mem_support_fundamentalPointCycle x

example [IsNoetherian X] (x : genericPoints X) :
    0 < fundamentalCycle X (IntegralClosedSubscheme.pointClosure x.val) := by
  rw [fundamentalCycle_component]
  exact_mod_cast genericMultiplicity_pos x

example [IsNoetherian X] [IsReduced X] (x : genericPoints X) :
    fundamentalCycle X (IntegralClosedSubscheme.pointClosure x.val) = 1 :=
  fundamentalCycle_component_of_isReduced x

example [IsNoetherian X] [IrreducibleSpace X] :
    fundamentalCycle X =
      Finsupp.single (IntegralClosedSubscheme.pointClosure (genericPoint X))
        ((Module.length (X.presheaf.stalk (genericPoint X))
          (X.presheaf.stalk (genericPoint X))).toNat : ℤ) :=
  fundamentalCycle_of_irreducibleSpace

example [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsIso f] :
    IntegralCycle.finitePushforward f (fundamentalCycle X) = fundamentalCycle Y :=
  finitePushforward_fundamentalCycle f

example [IsNoetherian X] (I : X.IdealSheafData) (x : genericPoints I.subscheme) :
    closedFundamentalCycle I (IntegralClosedSubscheme.pointClosure (I.subschemeι x.val)) =
      (genericMultiplicity x : ℤ) :=
  closedFundamentalCycle_component I x

example [IsNoetherian X] (V : IntegralClosedSubscheme X) :
    closedFundamentalCycle V.val = Finsupp.single V 1 :=
  closedFundamentalCycle_of_isIntegral V.val

example (k : Type u) [Field k] :
    fundamentalCycle (Spec (.of k)) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure (genericPoint (Spec (.of k)))) 1 :=
  fundamentalCycle_of_isIntegral
