/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPoint
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichFiniteLifting

/-!
# Finite-support lifting in the actual Nisnevich-neighborhood index

A geometric pointed neighborhood with an isomorphic residue-field map defines
an object of the actual neighborhood category by applying the inverse of that
residue-field map. Thus existing finite-support lifting takes place inside the
index used to compute the smooth Nisnevich point fiber. The entire canonical
pullback support, its lift, and the displayed factorization equation are retained.

This is an interface for the finite-support construction of MVW's varying
closed-point envelope. It neither defines that envelope's transfer action nor
identifies it with a product over fixed site points. It depends on the existing
smooth-site geometry and is not a standalone upstream extraction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {U X : Scheme.{u}} (g : U ⟶ X) (u : U) {x : X} (h : g u = x)
  [IsIso (g.residueFieldMap u)]

/-- The canonical lift of a residue-field point through an isomorphic residue map. -/
def residueFieldPointLift : Spec (X.residueField x) ⟶ U :=
  Spec.map (inv (g.residueFieldMap u) ≫ (X.residueFieldCongr h).hom) ≫
    U.fromSpecResidueField u

/-- The lift uses the inverse actual residue-field map and lies over the original point. -/
@[reassoc (attr := simp)]
theorem residueFieldPointLift_comp :
    g.residueFieldPointLift u h ≫ g = X.fromSpecResidueField x := by
  simp only [residueFieldPointLift, Category.assoc,
    ← g.SpecMap_residueFieldMap_fromSpecResidueField u, ← Spec.map_comp_assoc,
    IsIso.hom_inv_id_assoc, Scheme.residueFieldCongr_fromSpecResidueField]

@[simp]
theorem residueFieldPointLift_apply (a : Spec (X.residueField x)) :
    g.residueFieldPointLift u h a = u := by
  simp [residueFieldPointLift]

end AlgebraicGeometry.Scheme.Hom

namespace Motivic.SmoothSite.NisnevichNeighborhood

variable {S : Scheme.{u}} {X U : SmoothSite S} {x : X.left}

set_option backward.isDefEq.respectTransparency false in
/-- Convert a genuine pointed étale map to the actual neighborhood index, using
its isomorphic residue-field map rather than choosing a new field embedding. -/
def ofResidueFieldIso (g : U ⟶ X) [Etale g.left] (u : U.left) (h : g.left u = x)
    [IsIso (g.left.residueFieldMap u)] : NisnevichNeighborhood X x :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk g.left)
    (Over.homMk (g.left.residueFieldPointLift u h) (g.left.residueFieldPointLift_comp u h)),
    by
      change smoothSeparatedFiniteType (g.left ≫ X.hom)
      rw [MorphismProperty.Over.w]
      exact U.prop⟩

@[simp]
theorem ofResidueFieldIso_hom (g : U ⟶ X) [Etale g.left] (u : U.left)
    (h : g.left u = x) [IsIso (g.left.residueFieldMap u)] :
    (ofResidueFieldIso g u h).obj.obj.hom = g.left := rfl

@[simp]
theorem ofResidueFieldIso_point (g : U ⟶ X) [Etale g.left] (u : U.left)
    (h : g.left u = x) [IsIso (g.left.residueFieldMap u)] :
    (ofResidueFieldIso g u h).obj.val.left = g.left.residueFieldPointLift u h := rfl

/-- The actual structural arrow of a pointed neighborhood in the smooth site. -/
def toBase (N : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodFunctor X x).obj N ⟶ X := homMk N.obj.obj.hom rfl

@[simp]
theorem toBase_left (N : NisnevichNeighborhood X x) : N.toBase.left = N.obj.obj.hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The whole finite support lifts over an object of the actual point-fiber index.
The support can be nonreduced or nonflat, and its fiber can be empty. -/
theorem exists_lift_of_isFinite [IsAffine S]
    {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = x → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (N : NisnevichNeighborhood X x) (b : pullback p N.obj.obj.hom ⟶ V),
      b ≫ q = pullback.fst p N.obj.obj.hom := by
  obtain ⟨U, g, hg, u, hu, hr, b, hb⟩ :=
    SmoothSite.exists_nisnevich_lift_of_isFinite X p x q hq
  exact ⟨ofResidueFieldIso g u hu, b, hb⟩

end Motivic.SmoothSite.NisnevichNeighborhood
