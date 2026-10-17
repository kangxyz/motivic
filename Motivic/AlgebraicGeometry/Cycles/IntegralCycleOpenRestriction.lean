/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FundamentalInvariance
public import Motivic.AlgebraicGeometry.Cycles.GenericStalkPoints
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual integral-cycle restriction to an open subscheme

The faithful point dictionary ranges over ALL points, not just component
points. Restriction is coefficient restriction along the actual open inclusion.
A retained integral support is the literal pullback ideal sheaf; a support
whose generic point is omitted has empty intersection with the open.

The fundamental-cycle identity uses the original open-stalk isomorphism and
therefore retains nilpotent multiplicities. Finite pushforward commutes with
restriction by the actual morphismRestrict square and its residue-field tower.
No finite morphism is presumed to preserve component generic points.

SOURCE-ONLY PROPOSAL: no compilation or acceptance is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

namespace IntegralClosedSubscheme

variable {X : Scheme.{u}} (W : IntegralClosedSubscheme X) (U : X.Opens)

/-- The integral support retained by an open containing its generic point. -/
def openRestriction (h : W.point ∈ U) : IntegralClosedSubscheme U.toScheme :=
  pointClosure ⟨W.point, h⟩

@[simp] theorem point_openRestriction (h : W.point ∈ U) :
    (W.openRestriction U h).point = ⟨W.point, h⟩ :=
  point_pointClosure _

/-- The closed support is exactly the intersection with the actual open. -/
theorem support_openRestriction (h : W.point ∈ U) :
    ((W.openRestriction U h).val.support : Set U.toScheme) =
      U.ι ⁻¹' (W.val.support : Set X) := by
  rw [openRestriction, support_pointClosure,
    U.ι.isOpenEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
  exact congrArg (fun s : Set X => U.ι ⁻¹' s) W.point_spec.def

/-- A removed generic point means the entire integral closed support misses the open. -/
theorem support_preimage_eq_empty_of_point_not_mem (h : W.point ∉ U) :
    U.ι ⁻¹' (W.val.support : Set X) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hs : W.point ⤳ x.1 := by
    rw [specializes_iff_mem_closure, W.point_spec.def]
    exact hx
  exact h (hs.mem_open U.isOpen x.2)

/-- The retained reduced support is the ACTUAL restricted ideal sheaf,
not merely a support with an abstractly equivalent carrier. -/
theorem openRestriction_val (h : W.point ∈ U) :
    (W.openRestriction U h).val = W.val.comap U.ι := by
  let i := (W.val.comapIso U.ι).hom ≫ pullback.snd U.ι W.val.subschemeι
  have : IsOpenImmersion i := by dsimp only [i]; infer_instance
  have : IsReduced (W.val.comap U.ι).subscheme := isReduced_of_isOpenImmersion i
  apply idealSheaf_eq_of_support_eq
  apply SetLike.coe_injective
  simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage] using
    W.support_openRestriction U h

end IntegralClosedSubscheme

namespace FiniteSupportCycle

variable {X Y : Scheme.{u}}

/-- Coefficient restriction along the literal inclusion of an open subscheme. -/
def openRestriction (U : X.Opens) : FiniteSupportCycle X →+ FiniteSupportCycle U.toScheme :=
  Finsupp.comapDomain.addMonoidHom U.ι.isOpenEmbedding.injective

@[simp] theorem openRestriction_apply (U : X.Opens) (c : FiniteSupportCycle X)
    (x : U.toScheme) : openRestriction U c x = c x.1 := rfl

/-- A point inside the open is retained, with its arbitrary signed coefficient. -/
theorem openRestriction_single_of_mem (U : X.Opens) (x : X) (hx : x ∈ U) (n : ℤ) :
    openRestriction U (Finsupp.single x n) = Finsupp.single ⟨x, hx⟩ n :=
  Finsupp.comapDomain_single U.ι ⟨x, hx⟩ n _

/-- A point outside the open contributes nothing. -/
theorem openRestriction_single_of_not_mem (U : X.Opens) (x : X) (hx : x ∉ U) (n : ℤ) :
    openRestriction U (Finsupp.single x n) = 0 := by
  apply Finsupp.comapDomain_single_of_not_mem_range
  rintro ⟨y, rfl⟩
  exact hx y.2

/-- The original restriction square identifies the actual residue degree.
The two open inclusions have degree one; no field-extension invariance is assumed. -/
theorem residueDegree_morphismRestrict (f : X ⟶ Y) (V : Y.Opens)
    (x : (f ⁻¹ᵁ V).toScheme) : (f ∣_ V).residueDegree x = f.residueDegree x.1 := by
  have h := congrArg (fun m => m.residueDegree x) (morphismRestrict_ι f V)
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks,
    one_mul, mul_one, Scheme.Opens.ι_apply] using h

/-- Every stalk scalar map is the actual one in the open-restriction square. -/
def morphismRestrictStalkArrowIso (f : X ⟶ Y) (V : Y.Opens)
    (x : (f ⁻¹ᵁ V).toScheme) :
    Arrow.mk ((f ∣_ V).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) :=
  morphismRestrictStalkMap f V x

/-- The all-point collision sum commutes with restriction, including the
outside-open branch. This numerical identity itself needs no finiteness assumption. -/
theorem openRestriction_residuePushforward (f : X ⟶ Y) (V : Y.Opens) :
    (openRestriction V).comp (residuePushforward f) =
      (residuePushforward (f ∣_ V)).comp (openRestriction (f ⁻¹ᵁ V)) := by
  apply Finsupp.addHom_ext
  intro x n
  by_cases hx : f x ∈ V
  · simp only [AddMonoidHom.comp_apply, residuePushforward_single,
      openRestriction_single_of_mem V (f x) hx,
      openRestriction_single_of_mem (f ⁻¹ᵁ V) x hx]
    have hpoint : (f ∣_ V) ⟨x, hx⟩ = ⟨f x, hx⟩ :=
      Subtype.ext (morphismRestrict_base_coe f V ⟨x, hx⟩)
    rw [hpoint, residueDegree_morphismRestrict]
  · simp only [AddMonoidHom.comp_apply, residuePushforward_single,
      openRestriction_single_of_not_mem V (f x) hx,
      openRestriction_single_of_not_mem (f ⁻¹ᵁ V) x hx, map_zero]

end FiniteSupportCycle

namespace IntegralCycle

variable {X Y Z : Scheme.{u}}

/-- The inverse of the faithful dictionary, on ALL scheme points. -/
def fromPoints : FiniteSupportCycle X →+ IntegralCycle X :=
  Finsupp.mapDomain.addMonoidHom IntegralClosedSubscheme.pointClosure

@[simp] theorem fromPoints_single (x : X) (n : ℤ) :
    fromPoints (Finsupp.single x n) =
      Finsupp.single (IntegralClosedSubscheme.pointClosure x) n :=
  Finsupp.mapDomain_single

@[simp] theorem toPoints_fromPoints (c : FiniteSupportCycle X) : toPoints (fromPoints c) = c := by
  change Finsupp.mapDomain IntegralClosedSubscheme.point
    (Finsupp.mapDomain IntegralClosedSubscheme.pointClosure c) = c
  rw [← Finsupp.mapDomain_comp]
  simpa only [Function.comp_def, IntegralClosedSubscheme.point_pointClosure, id_eq] using
    Finsupp.mapDomain_id (v := c)

@[simp] theorem fromPoints_toPoints (c : IntegralCycle X) : fromPoints (toPoints c) = c := by
  apply toPoints_injective
  rw [toPoints_fromPoints]

/-- Actual open restriction on integral ideal-sheaf cycles. -/
def openRestriction (U : X.Opens) : IntegralCycle X →+ IntegralCycle U.toScheme :=
  fromPoints.comp ((FiniteSupportCycle.openRestriction U).comp toPoints)

@[simp] theorem toPoints_openRestriction (U : X.Opens) (c : IntegralCycle X) :
    toPoints (openRestriction U c) = FiniteSupportCycle.openRestriction U (toPoints c) := by
  exact toPoints_fromPoints _

/-- The coefficient at every actual open point is unchanged, also off the generic locus. -/
theorem toPoints_openRestriction_apply (U : X.Opens) (c : IntegralCycle X)
    (x : U.toScheme) : toPoints (openRestriction U c) x = toPoints c x.1 := by
  rw [toPoints_openRestriction, FiniteSupportCycle.openRestriction_apply]

/-- A retained generator has exactly the actual restricted ideal sheaf proved above. -/
theorem openRestriction_single_of_mem (U : X.Opens) (W : IntegralClosedSubscheme X)
    (h : W.point ∈ U) (n : ℤ) :
    openRestriction U (Finsupp.single W n) =
      Finsupp.single (W.openRestriction U h) n := by
  apply toPoints_injective
  rw [toPoints_openRestriction, toPoints_single,
    FiniteSupportCycle.openRestriction_single_of_mem U W.point h,
    toPoints_single, IntegralClosedSubscheme.point_openRestriction]

/-- A support missing the open is removed, for every integer coefficient. -/
theorem openRestriction_single_of_not_mem (U : X.Opens) (W : IntegralClosedSubscheme X)
    (h : W.point ∉ U) (n : ℤ) : openRestriction U (Finsupp.single W n) = 0 := by
  apply toPoints_injective
  rw [toPoints_openRestriction, toPoints_single,
    FiniteSupportCycle.openRestriction_single_of_not_mem U W.point h, map_zero]

/-- The actual pushforward square through the point dictionary, evaluated on a cycle. -/
theorem toPoints_finitePushforward_apply (f : X ⟶ Y) [IsFinite f] (c : IntegralCycle X) :
    toPoints (finitePushforward f c) = FiniteSupportCycle.residuePushforward f (toPoints c) :=
  DFunLike.congr_fun (toPoints_finitePushforward f) c

/-- Finite pushforward commutes with the actual target-open restriction.
The proof retains all source points and all collisions, without generic-preservation input. -/
theorem openRestriction_finitePushforward (f : X ⟶ Y) [IsFinite f] (V : Y.Opens)
    (c : IntegralCycle X) :
    openRestriction V (finitePushforward f c) =
      finitePushforward (f ∣_ V) (openRestriction (f ⁻¹ᵁ V) c) := by
  apply toPoints_injective
  rw [toPoints_openRestriction, toPoints_finitePushforward_apply,
    toPoints_finitePushforward_apply, toPoints_openRestriction]
  exact DFunLike.congr_fun (FiniteSupportCycle.openRestriction_residuePushforward f V)
    (toPoints c)

/-- Open restriction preserves the whole fundamental cycle, including every
nonreduced generic-stalk length. Both directions of genericity are proved. -/
theorem openRestriction_fundamentalCycle (U : X.Opens)
    [IsNoetherian X] [IsNoetherian U.toScheme] :
    openRestriction U (fundamentalCycle X) = fundamentalCycle U.toScheme := by
  apply toPoints_injective
  ext x
  simp only [toPoints_openRestriction_apply, toPoints_fundamentalCycle,
    fundamentalPointCycle_apply]
  have hg : x.1 ∈ genericPoints X ↔ x ∈ genericPoints U.toScheme :=
    ⟨mem_genericPoints_of_isOpenImmersion U.ι x,
      mem_genericPoints_of_generalizing U.ι U.ι.isOpenEmbedding.generalizingMap x⟩
  by_cases hx : x ∈ genericPoints U.toScheme
  · rw [dite_eq_left (hg.mpr hx), dite_eq_left hx]
    unfold genericMultiplicity
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
      (stalk_length_eq_of_isOpenImmersion U.ι x)
  · rw [dite_eq_right (mt hg.mp hx), dite_eq_right hx]

/-- A finite support immersion can be restricted before or after taking its
full fundamental cycle; this is the component-exterior attachment interface. -/
theorem openRestriction_finitePushforward_fundamentalCycle
    (f : X ⟶ Y) [IsFinite f] (V : Y.Opens)
    [IsNoetherian X] [IsNoetherian (f ⁻¹ᵁ V).toScheme] :
    openRestriction V (finitePushforward f (fundamentalCycle X)) =
      finitePushforward (f ∣_ V) (fundamentalCycle (f ⁻¹ᵁ V).toScheme) := by
  rw [openRestriction_finitePushforward, openRestriction_fundamentalCycle]

/-- The restricted composite is the literal composite of restricted finite
maps, so its pushforward uses the same actual residue-field towers. -/
theorem finitePushforward_morphismRestrict_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] (V : Z.Opens) :
    finitePushforward ((f ≫ g) ∣_ V) =
      (finitePushforward (g ∣_ V)).comp (finitePushforward (f ∣_ (g ⁻¹ᵁ V))) := by
  have hcongr {A B : Scheme.{u}} (p q : A ⟶ B) (hp : IsFinite p)
      (hq : IsFinite q) (h : p = q) :
      @finitePushforward A B p hp = @finitePushforward A B q hq := by
    cases h
    rfl
  exact (hcongr ((f ≫ g) ∣_ V) (f ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V)
    inferInstance inferInstance (morphismRestrict_comp f g V)).trans
      (finitePushforward_comp (f ∣_ (g ⁻¹ᵁ V)) (g ∣_ V))

end IntegralCycle

end Motivic
