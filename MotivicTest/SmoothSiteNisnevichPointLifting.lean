/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Lifting
public import Lean.Util.CollectAxioms

/-!
# Consumers of finite-support lifting in the neighborhood index

The actual inverse residue map, canonical field-valued point, and the complete
finite support are retained. No smoothness, reducedness or flatness is imposed
on the support; no algebraic closure is imposed on the base field.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open  _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

section ResiduePoint

variable {U X : Scheme.{u}} (g : U ⟶ X) (u : U) {x : X} (h : g u = x)
  [IsIso (g.residueFieldMap u)]

example : g.residueFieldPointLift u h =
    Spec.map (inv (g.residueFieldMap u) ≫ (X.residueFieldCongr h).hom) ≫
      U.fromSpecResidueField u := rfl

example : g.residueFieldPointLift u h ≫ g = X.fromSpecResidueField x :=
  g.residueFieldPointLift_comp u h

example (a : Spec (X.residueField x)) : g.residueFieldPointLift u h a = u :=
  g.residueFieldPointLift_apply u h a

end ResiduePoint

section Neighborhood

variable {S : Scheme.{u}} {X U : SmoothSite S} {x : X.left}
  (g : U ⟶ X) [Etale g.left] (u : U.left) (h : g.left u = x)
  [IsIso (g.left.residueFieldMap u)]

example : (NisnevichNeighborhood.ofResidueFieldIso g u h).obj.obj.hom = g.left := rfl

example : (NisnevichNeighborhood.ofResidueFieldIso g u h).obj.val.left ≫ g.left =
    X.left.fromSpecResidueField x := g.left.residueFieldPointLift_comp u h

example (N : NisnevichNeighborhood X x) :
    N.toBase.left = N.obj.obj.hom := rfl

end Neighborhood

section FiniteSupport

variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
  (q : V ⟶ Z) [Etale q] [IsSeparated q]
  (hq : ∀ z : Z, p z = x → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v))

example : ∃ (N : NisnevichNeighborhood X x) (b : pullback p N.toBase.left ⟶ V),
    b ≫ q = pullback.fst p N.toBase.left :=
  NisnevichNeighborhood.exists_lift_of_isFinite p q hq

end FiniteSupport

open Lean in
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood in
run_cmd do
  for name in #[``AlgebraicGeometry.Scheme.Hom.residueFieldPointLift,
      ``AlgebraicGeometry.Scheme.Hom.residueFieldPointLift_comp,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.ofResidueFieldIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood.toBase,
      ``exists_lift_of_isFinite] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Point-indexed finite-support lifting uses only standard Lean foundations."
