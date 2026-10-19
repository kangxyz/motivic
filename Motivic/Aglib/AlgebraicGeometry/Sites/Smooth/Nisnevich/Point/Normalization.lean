/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.QuasiFinite.Fibers.FiniteClosedFiberNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Lifting

/-!
# Normalized pointed neighborhoods over finite closed-center sets

A pointed étale neighborhood can have additional points above its chosen
center. For a finite selected set of closed target centers, we give an actual
affine open refinement which retains the original canonical residue-field lift
and has exactly its distinguished point above the entire selected set.

This supplies branch control for representatives of the finitely many germs
needed by a correspondence at a closed source point. No cover of the entire
target, transfer action, or representative-independence assertion is used.
This module depends on the existing smooth site and is not a standalone
upstream extraction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

variable {S : Scheme.{u}} {X : SmoothSite S} {x : X.left}

/-- The distinguished point supplied by the actual canonical residue-field lift. -/
def center (N : NisnevichNeighborhood X x) : N.obj.obj.left :=
  N.obj.val.left (default : Spec (X.left.residueField x))

@[simp]
theorem toBase_center (N : NisnevichNeighborhood X x) :
    (dsimp% only [Functor.id_obj, Functor.const_obj_obj]
      N.obj.obj.hom N.center) = x := by
  change N.toBase.left N.center = x
  have h := congrArg (fun f : Spec (X.left.residueField x) ⟶ X.left ↦ f default)
    (Over.w N.obj.val)
  change N.toBase.left N.center = X.left.fromSpecResidueField x default at h
  simpa only [Scheme.fromSpecResidueField_apply] using h

/-- Every actual neighborhood refinement preserves the chosen field-valued point. -/
@[reassoc]
theorem refinement_point {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    M.obj.val.left ≫ q.hom.hom.left = N.obj.val.left := by
  have h := q.hom.map_val
  exact congrArg (fun f ↦ f.left) h

@[simp]
theorem refinement_center {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    q.hom.hom.left M.center = N.center :=
  congrArg (fun f : Spec (X.left.residueField x) ⟶ N.obj.obj.left ↦ f default)
    (refinement_point q)

set_option backward.isDefEq.respectTransparency false in
/-- An affine pointed open refinement has just the chosen branch above the
selected finite closed-center set. The field-valued point and refinement are literal maps. -/
theorem exists_normalized_refinement [IsAffine S] (N : NisnevichNeighborhood X x)
    (T : Set X.left) (hT : T.Finite) (hclosed : ∀ y ∈ T, IsClosed ({y} : Set X.left))
    (hx : x ∈ T) :
    ∃ (M : NisnevichNeighborhood X x) (q : M ⟶ N),
      IsAffine M.obj.obj.left ∧ IsOpenImmersion q.hom.hom.left ∧
      M.obj.val.left ≫ q.hom.hom.left = N.obj.val.left ∧
      M.toBase.left ⁻¹' T = {M.center} := by
  have : QuasiCompact N.obj.obj.hom := inferInstanceAs (QuasiCompact N.toBase.left)
  have := N.obj.obj.hom.locallyQuasiFinite_of_etale
  obtain ⟨R, j, _, hj, hbranch⟩ :=
    N.obj.obj.hom.exists_affine_isolating_finite_closed_fibers T hT hclosed N.center
  let y : Spec (X.left.residueField x) ⟶ N.obj.obj.left := N.obj.val.left
  have hy : Set.range y ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let y' := IsOpenImmersion.lift j y hy
  have hy' : y' ≫ j = N.obj.val.left := IsOpenImmersion.lift_fac j y hy
  let M₀ : PointedEtaleNeighborhood X x :=
    Functor.elementsMk _ (Scheme.Etale.mk (j ≫ N.obj.obj.hom))
      (Over.homMk y' (by simpa [← Category.assoc, hy'] using Over.w N.obj.val))
  have hM : smoothNeighborhoodProperty X x M₀ := by
    change smoothSeparatedFiniteType ((j ≫ N.obj.obj.hom) ≫ X.hom)
    have : IsAffineHom ((j ≫ N.obj.obj.hom) ≫ X.hom) := isAffineHom_of_isAffine (Y := S) _
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let M : NisnevichNeighborhood X x := ⟨M₀, hM⟩
  let q : M ⟶ N := ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk j rfl) (by
      apply Over.OverMorphism.ext
      exact hy'))
  refine ⟨M, q, inferInstanceAs (IsAffine (Spec R)), inferInstanceAs (IsOpenImmersion j),
    hy', ?_⟩
  apply Set.Subset.antisymm
  · intro v hv
    apply (j.isOpenEmbedding.injective)
    exact (hbranch v hv).trans (refinement_center q).symm
  · rintro v (rfl : v = M.center)
    change M.obj.obj.hom M.center ∈ T
    simpa only [show M.obj.obj.hom M.center = x from M.toBase_center] using hx

end AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
