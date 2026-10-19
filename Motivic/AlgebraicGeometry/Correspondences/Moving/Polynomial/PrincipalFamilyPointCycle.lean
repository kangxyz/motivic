/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamily
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.Equality


/-!
# The original principal family in the native point-cycle endpoint interface

Both producers use the same original point closures, retained-open lifts,
finite images and residue degrees. The equality below exposes the existing
no-extra-flatness graph endpoint theorem without replacing the principal cycle
or reproving the generator intersection calculation.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open AlgebraicGeometry.PrincipalFamilyUnitOpen
open scoped BigOperators

universe u

namespace Motivic.PrincipalOrderCorrespondence

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  [IsAffine X.left] {C V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [V.IsQuasiAffine] (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
  (h : Γ(C, U)) (hh : IsUnit h)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The original principal-order producer equals the general point-cycle
producer, with precisely the same support, maps, images and weighted degrees. -/
theorem correspondence_eq_finitePointCycle :
    correspondence q j U hU h hh g hbase =
      FinitePointCycleCorrespondence.correspondence q j
          (_root_.AlgebraicGeometry.Scheme.principalOrderCycle U h hh)
        (_root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_range j U hU h hh)
        (fun x => _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_isFinite q j U hU h hh
            x.val
          (Finsupp.mem_support_iff.mp x.property))
        (fun x => _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_dominates_component q
            j U hU h hh x.val
          (Finsupp.mem_support_iff.mp x.property)) g hbase := by
  classical
  unfold correspondence FinitePointCycleCorrespondence.correspondence
  simp only [_root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply]
  rfl

end Motivic.PrincipalOrderCorrespondence

namespace Motivic.PrincipalFamilyCorrespondence

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  [IsAffine X.left] {C V W B : Scheme.{u}}
  (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  [AlgebraicGeometry.IsIntegral (parameterSpace (q ≫ X.hom))]
  [AlgebraicGeometry.IsNoetherian (parameterSpace (q ≫ X.hom))]
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

/-- The actual principal family in the general point-cycle interface, with
all original support geometry constructed by the principal-order producer. -/
def pointCycleCorrespondence :
    Cor.mk (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) ⟶
        Cor.mk Y := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsAffineHom (projection X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let : IsAffine (parameterSpace X.hom) := isAffine_of_isAffineHom (projection X.hom)
  let U := ambientUnitOpen (q ≫ X.hom) v f
  let s := ambientUnitSection (q ≫ X.hom) v f
  let : Nonempty U := nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  let cover := complement_subset_ambientUnitOpen (q ≫ X.hom) j v b hcover f hf
  exact FinitePointCycleCorrespondence.correspondence
    (X := _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X)
    (familyProjection X q) (retainedInclusion X q j)
    (_root_.AlgebraicGeometry.Scheme.principalOrderCycle U s (isUnit_ambientUnitSection (q ≫ X.hom)
        v f))
    (_root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_range (retainedInclusion X q j) U
        cover s
      (isUnit_ambientUnitSection (q ≫ X.hom) v f))
    (fun x => _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_isFinite (familyProjection
        X q)
      (retainedInclusion X q j) U cover s
      (isUnit_ambientUnitSection (q ≫ X.hom) v f) x.val
      (Finsupp.mem_support_iff.mp x.property))
    (fun x => _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_dominates_component
        (familyProjection X q)
      (retainedInclusion X q j) U cover s
      (isUnit_ambientUnitSection (q ≫ X.hom) v f) x.val
      (Finsupp.mem_support_iff.mp x.property))
    (projection (j ≫ (q ≫ X.hom)) ≫ g) (family_base X Y q j g hbase)

/-- The exact native principal-order call underlying the original family. -/
def principalOrderPresentation :
    Cor.mk (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) ⟶
        Cor.mk Y := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsAffineHom (projection X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let : IsAffine (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite
      X).left :=
    isAffine_of_isAffineHom (projection X.hom)
  let U := ambientUnitOpen (q ≫ X.hom) v f
  let : Nonempty U := nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  exact PrincipalOrderCorrespondence.correspondence (familyProjection X q)
    (retainedInclusion X q j) U
    (complement_subset_ambientUnitOpen (q ≫ X.hom) j v b hcover f hf)
    (ambientUnitSection (q ≫ X.hom) v f)
    (isUnit_ambientUnitSection (q ≫ X.hom) v f)
    (projection (j ≫ (q ≫ X.hom)) ≫ g) (family_base X Y q j g hbase)

attribute [local irreducible] correspondence pointCycleCorrespondence principalOrderPresentation

/-- A producer-facing reduction of the original family, without expanding any
point-image generator or finite-support construction. -/
theorem correspondence_eq_principalOrderPresentation :
    correspondence X Y q j v b hcover f hf g hbase =
      principalOrderPresentation X Y q j v b hcover f hf g hbase := by
  unfold correspondence principalOrderPresentation
  rfl

/-- The exact principal-order call is the point-cycle call by the already
proved generic producer equality. -/
theorem principalOrderPresentation_eq_pointCycle :
    principalOrderPresentation X Y q j v b hcover f hf g hbase =
      pointCycleCorrespondence X Y q j v b hcover f hf g hbase := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsAffineHom (projection X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let : IsAffine (parameterSpace X.hom) := isAffine_of_isAffineHom (projection X.hom)
  let : IsAffine (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite
      X).left :=
    inferInstanceAs (IsAffine (parameterSpace X.hom))
  let U := ambientUnitOpen (q ≫ X.hom) v f
  let : Nonempty U := nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  unfold principalOrderPresentation pointCycleCorrespondence
  exact PrincipalOrderCorrespondence.correspondence_eq_finitePointCycle
    (X := _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLineSite X) (Y :=
        Y)
    (familyProjection X q) (retainedInclusion X q j) U
    (complement_subset_ambientUnitOpen (q ≫ X.hom) j v b hcover f hf)
    (ambientUnitSection (q ≫ X.hom) v f)
    (isUnit_ambientUnitSection (q ≫ X.hom) v f)
    (projection (j ≫ (q ≫ X.hom)) ≫ g) (family_base X Y q j g hbase)

/-- Equality with the original family retains its literal signed order cycle
and every finite-image residue degree. -/
theorem correspondence_eq_originalPointCycle :
    correspondence X Y q j v b hcover f hf g hbase =
      pointCycleCorrespondence X Y q j v b hcover f hf g hbase :=
  (correspondence_eq_principalOrderPresentation X Y q j v b hcover f hf g hbase).trans
    (principalOrderPresentation_eq_pointCycle X Y q j v b hcover f hf g hbase)

end Motivic.PrincipalFamilyCorrespondence
