/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.ClosedSubscheme

/-! # Consumers of actual generic-stalk fundamental cycles -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

variable {X Y : Scheme.{u}}

example (x : X) : (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x).point = x
    :=
  _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.point_pointClosure x

example (I : X.IdealSheafData) : IsReduced I.radical.subscheme := inferInstance

example [IsLocallyNoetherian X] (x : genericPoints X) :
    IsArtinianRing (X.presheaf.stalk x.val) :=
  _root_.AlgebraicGeometry.Scheme.isArtinianRing_stalk_of_mem_genericPoints x.val x.property

example [IsLocallyNoetherian X] (x : genericPoints X) :
    (_root_.AlgebraicGeometry.Scheme.genericMultiplicity x : ℕ∞) =
      Module.length (X.presheaf.stalk x.val) (X.presheaf.stalk x.val) :=
  _root_.AlgebraicGeometry.Scheme.genericMultiplicity_eq_length x

example [IsLocallyNoetherian X] (x : genericPoints X) (M : Type v) [AddCommGroup M]
    [Module (X.presheaf.stalk x.val) M] [Module.Finite (X.presheaf.stalk x.val) M] :
    Module.length (X.presheaf.stalk x.val) M ≠ ⊤ :=
  _root_.AlgebraicGeometry.Scheme.stalk_module_length_ne_top_of_mem_genericPoints x.val x.property M

example [IsNoetherian X] (x : X) :
    x ∈ (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle X).support ↔ x ∈ genericPoints X :=
  _root_.AlgebraicGeometry.Scheme.mem_support_fundamentalPointCycle x

example [IsNoetherian X] (x : genericPoints X) :
    0 < _root_.AlgebraicGeometry.Scheme.fundamentalCycle X
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val) := by
  rw [_root_.AlgebraicGeometry.Scheme.fundamentalCycle_component]
  exact_mod_cast _root_.AlgebraicGeometry.Scheme.genericMultiplicity_pos x

example [IsNoetherian X] [IsReduced X] (x : genericPoints X) :
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle X
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x.val) = 1 :=
  _root_.AlgebraicGeometry.Scheme.fundamentalCycle_component_of_isReduced x

example [IsNoetherian X] [IrreducibleSpace X] :
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle X =
      Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          (genericPoint X))
        ((Module.length (X.presheaf.stalk (genericPoint X))
          (X.presheaf.stalk (genericPoint X))).toNat : ℤ) :=
  _root_.AlgebraicGeometry.Scheme.fundamentalCycle_of_irreducibleSpace

example [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsIso f] :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward f
        (_root_.AlgebraicGeometry.Scheme.fundamentalCycle X) =
        _root_.AlgebraicGeometry.Scheme.fundamentalCycle Y :=
  _root_.AlgebraicGeometry.Scheme.finitePushforward_fundamentalCycle f

example [IsNoetherian X] (I : X.IdealSheafData) (x : genericPoints I.subscheme) :
    _root_.AlgebraicGeometry.Scheme.closedFundamentalCycle I
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (I.subschemeι x.val))
        =
      (_root_.AlgebraicGeometry.Scheme.genericMultiplicity x : ℤ) :=
  _root_.AlgebraicGeometry.Scheme.closedFundamentalCycle_component I x

example [IsNoetherian X] (V : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme X) :
    _root_.AlgebraicGeometry.Scheme.closedFundamentalCycle V.val = Finsupp.single V 1 :=
  _root_.AlgebraicGeometry.Scheme.closedFundamentalCycle_of_isIntegral V.val

example (k : Type u) [Field k] :
    _root_.AlgebraicGeometry.Scheme.fundamentalCycle (Spec (.of k)) =
      Finsupp.single (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          (genericPoint (Spec (.of k)))) 1 :=
  _root_.AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral
