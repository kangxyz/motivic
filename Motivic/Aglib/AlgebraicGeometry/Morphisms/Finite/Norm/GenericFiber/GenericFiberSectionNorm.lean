/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberDenseOpen
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-!
# Norm of a section on a dense open through the actual generic fiber

The original finite morphism and its literal generic pullback define the norm.
Only the target is integral. The whole source may be disconnected or nonreduced.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberSectionNorm`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartNorm`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
variable {C T : Scheme.{u}} [NoetherianSpace C] [IsIntegral T]
  (f : C ⟶ T) [IsFinite f]

/-- The actual generic projection lifts to a globally dense source open. -/
def genericFiberDenseOpenLift (W : C.Opens) (hW : Dense (W : Set C)) :
    pullback f (T.fromSpecStalk (genericPoint T)) ⟶ W :=
  IsOpenImmersion.lift W.ι (pullback.fst f (T.fromSpecStalk (genericPoint T)))
    (generic_pullback_range_subset_dense_open f W hW)

@[reassoc (attr := simp)]
theorem genericFiberDenseOpenLift_ι (W : C.Opens) (hW : Dense (W : Set C)) :
    genericFiberDenseOpenLift f W hW ≫ W.ι =
      pullback.fst f (T.fromSpecStalk (genericPoint T)) :=
  IsOpenImmersion.lift_fac _ _ _

/-- Restricting the dense domain does not change the actual generic lift. -/
theorem genericFiberDenseOpenLift_homOfLE {V W : C.Opens}
    (hV : Dense (V : Set C)) (hW : Dense (W : Set C)) (e : V ≤ W) :
    genericFiberDenseOpenLift f V hV ≫ C.homOfLE e = genericFiberDenseOpenLift f W hW := by
  apply (cancel_mono W.ι).mp
  simp only [Category.assoc, homOfLE_ι, genericFiberDenseOpenLift_ι]

set_option backward.isDefEq.respectTransparency false in
/-- The determinant norm of the same section restricted to the whole generic
fiber. Its coordinate algebra is automatically finite-dimensional over the
actual target function field, not a supplied globally free source module. -/
def genericFiberSectionNorm (W : C.Opens) (hW : Dense (W : Set C)) :
    Γ(C, W) →* T.functionField :=
  let q := pullback.snd f (T.fromSpecStalk (genericPoint T))
  let : IsFinite q := by dsimp [q]; infer_instance
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
  let : Module.Finite T.functionField
      Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    FiniteSchemeNormBaseChange.sections_finite
      (pullback.snd f (T.fromSpecStalk (genericPoint T)))
  (Algebra.norm T.functionField).comp
    (((genericFiberDenseOpenLift f W hW).appTop.hom.comp W.topIso.inv.hom).toMonoidHom)

set_option backward.isDefEq.respectTransparency false in
/-- The norm is independent of shrinking its globally dense open domain,
with the original sheaf restriction map on sections. -/
theorem genericFiberSectionNorm_restrict {V W : C.Opens}
    (hV : Dense (V : Set C)) (hW : Dense (W : Set C)) (e : V ≤ W) (s : Γ(C, W)) :
    genericFiberSectionNorm f V hV (C.presheaf.map (homOfLE e).op s) =
      genericFiberSectionNorm f W hW s := by
  have ht : C.presheaf.map (homOfLE e).op ≫ V.topIso.inv =
      W.topIso.inv ≫ (C.homOfLE e).appTop := by
    simp only [Opens.topIso_inv, homOfLE_appTop]
    rw [← C.presheaf.map_comp, ← C.presheaf.map_comp]
    congr 1
  have hl := genericFiberDenseOpenLift_homOfLE f hV hW e
  have hh := congrArg (fun g => g.appTop) hl
  rw [Hom.comp_appTop] at hh
  have hc : (C.presheaf.map (homOfLE e).op ≫ V.topIso.inv) ≫
      (genericFiberDenseOpenLift f V hV).appTop =
      W.topIso.inv ≫ (genericFiberDenseOpenLift f W hW).appTop := by
    rw [ht, Category.assoc, hh]
  have he := congrArg (fun g : Γ(C, W) ⟶
      Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) => g s) hc
  exact congrArg (fun x =>
    let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd f (T.fromSpecStalk (genericPoint T)))).toAlgebra
    Algebra.norm T.functionField x) he

end AlgebraicGeometry.Scheme
