/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Sections.FiniteFlatGenericFiber
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Sections.GenericStalkSectionGlue

/-! # The original generic section extends to a generic-containing original open -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GenericSection
variable (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
  [IsNoetherianRing B] [IsFinite (baseMap R B)] [Flat (baseMap R B)]

/-- The actual generic fibre factors through every open containing the source generic points. -/
def genericFiberToOpen (O : (Spec (.of B)).Opens)
    (hO : genericPoints (Spec (.of B)) ⊆ (O : Set (Spec (.of B)))) :
    genericFiber R B ⟶ O.toScheme :=
  IsOpenImmersion.lift O.ι (pullback.fst (baseMap R B) (genericMap R)) (by
    rw [Opens.range_ι, genericFiber_range]
    exact hO)

omit [IsNoetherianRing B] in
@[reassoc (attr := simp)]
lemma genericFiberToOpen_ι (O : (Spec (.of B)).Opens)
    (hO : genericPoints (Spec (.of B)) ⊆ (O : Set (Spec (.of B)))) :
    genericFiberToOpen R B O hO ≫ O.ι = pullback.fst (baseMap R B) (genericMap R) :=
  IsOpenImmersion.lift_fac _ _ _

/-- Original generic sections, not merely isomorphic replacement sections, spread
on a genuine generic-containing open of the original finite flat scheme. -/
theorem exists_generic_open_section
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of B)) [LocallyOfFiniteType f]
    (s : genericFiber R B ⟶ Y)
    (hs : s ≫ f = pullback.fst (baseMap R B) (genericMap R)) :
    ∃ (O : (Spec (.of B)).Opens)
      (hO : genericPoints (Spec (.of B)) ⊆ (O : Set (Spec (.of B))))
      (t : O.toScheme ⟶ Y), t ≫ f = O.ι ∧ genericFiberToOpen R B O hO ≫ t = s := by
  let φ (x : genericPoints (Spec (.of B))) :=
    stalkToGenericFiber R B x.val (generic_comap_eq_bot R B x) ≫ s
  have hφ (x) : φ x ≫ f = (Spec (.of B)).fromSpecStalk x.val := by
    simp only [φ, Category.assoc, hs, stalkToGenericFiber_fst]
  obtain ⟨O, hO, t, ht, hval⟩ := exists_generic_open_section_of_stalk_sections f φ hφ
  refine ⟨O, hO, t, ht, ?_⟩
  apply hom_ext_of_fromSpecStalk
  intro z
  let x : genericPoints (Spec (.of B)) :=
    ⟨pullback.fst (baseMap R B) (genericMap R) z,
      (genericFiber_range R B).le ⟨z, rfl⟩⟩
  let a : Spec ((genericFiber R B).presheaf.stalk z) ⟶
      Spec ((Spec (.of B)).presheaf.stalk x.val) :=
    Spec.map ((pullback.fst (baseMap R B) (genericMap R)).stalkMap z)
  have ha : a ≫ stalkToGenericFiber R B x.val (generic_comap_eq_bot R B x) =
      (genericFiber R B).fromSpecStalk z := by
    apply (cancel_mono (pullback.fst (baseMap R B) (genericMap R))).mp
    rw [Category.assoc, stalkToGenericFiber_fst]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk _
  have hu : (genericFiber R B).fromSpecStalk z ≫ genericFiberToOpen R B O hO =
      a ≫ O.fromSpecStalkOfMem x.val (hO x.property) := by
    apply (cancel_mono O.ι).mp
    rw [Category.assoc, genericFiberToOpen_ι, Category.assoc, Opens.fromSpecStalkOfMem_ι]
    exact (Scheme.SpecMap_stalkMap_fromSpecStalk _).symm
  rw [← Category.assoc, hu, Category.assoc, hval]
  change a ≫ (stalkToGenericFiber R B x.val (generic_comap_eq_bot R B x) ≫ s) = _
  rw [← Category.assoc, ha]

end AlgebraicGeometry.Scheme.GenericSection
