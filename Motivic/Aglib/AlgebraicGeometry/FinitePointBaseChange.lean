/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorCyclePushforward
public import Motivic.Aglib.AlgebraicGeometry.FlatFundamentalCycleTower

/-!
# Whole finite-point pushforwards under arbitrary field change

A finite map between integral schemes finite over a field retains its original
residue degree on the full scalar-extended fundamental cycles. All components
and their original local lengths remain. Genericity is proved through the
finite projection to the new field, not assumed for an arbitrary finite map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FinitePointBaseChange

open IntegralClosedSubscheme

/-- The reduced closure of an integral scheme's generic point is the entire scheme. -/
instance genericPointClosure_isIso (X : Scheme.{u}) [IsIntegral X] :
    IsIso (pointClosure (genericPoint X)).val.subschemeι := by
  rw [Scheme.isIso_subschemeι_iff_eq_bot]
  change (Scheme.IdealSheafData.vanishingIdeal
    ⟨closure {genericPoint X}, isClosed_closure⟩).radical = ⊥
  have ht : (⟨closure {genericPoint X}, isClosed_closure⟩ :
      TopologicalSpace.Closeds X) = ⊤ := by
    apply SetLike.coe_injective
    exact (genericPoint_spec X).def
  rw [ht, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
    Scheme.IdealSheafData.radical_bot, Scheme.nilradical_eq_bot]

/-- Every point of a scheme finite over a field is an actual component generic. -/
theorem mem_genericPoints_of_finite {F : Type u} [Field F]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of F)) [IsFinite p] (x : X) :
    x ∈ genericPoints X := by
  apply Motivic.mem_genericPoints_of_image_generic p x
  rw [genericPoints_eq_singleton]
  exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {P Q : Scheme.{u}} (f : P ⟶ Q) (q : Q ⟶ Spec (.of k))

/-- The whole source, including every scalar-extended component. -/
abbrev source : Scheme.{u} := pullback (f ≫ q) (Spec.map (CommRingCat.ofHom φ))

/-- The whole target, before taking any reduced supports. -/
abbrev target : Scheme.{u} := pullback q (Spec.map (CommRingCat.ofHom φ))

/-- The literal scalar extension of the original finite morphism. -/
def map : source φ f q ⟶ target φ q :=
  pullback.lift
    (pullback.fst (f ≫ q) (Spec.map (CommRingCat.ofHom φ)) ≫ f)
    (pullback.snd (f ≫ q) (Spec.map (CommRingCat.ofHom φ))) (by
      simpa only [Category.assoc] using
        (pullback.condition (f := f ≫ q) (g := Spec.map (CommRingCat.ofHom φ))))

@[reassoc (attr := simp)]
theorem map_fst : map φ f q ≫ pullback.fst q (Spec.map (CommRingCat.ofHom φ)) =
    pullback.fst (f ≫ q) (Spec.map (CommRingCat.ofHom φ)) ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem map_snd : map φ f q ≫ pullback.snd q (Spec.map (CommRingCat.ofHom φ)) =
    pullback.snd (f ≫ q) (Spec.map (CommRingCat.ofHom φ)) :=
  pullback.lift_snd _ _ _

/-- The displayed square is Cartesian for the actual original morphism. -/
theorem isPullback :
    IsPullback (pullback.fst (f ≫ q) (Spec.map (CommRingCat.ofHom φ)))
      (map φ f q) f (pullback.fst q (Spec.map (CommRingCat.ofHom φ))) := by
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback q
    (Spec.map (CommRingCat.ofHom φ))) ?_ (map_fst φ f q).symm
  rw [map_snd]
  exact IsPullback.of_hasPullback (f ≫ q) (Spec.map (CommRingCat.ofHom φ))

instance map_isFinite [IsFinite f] : IsFinite (map φ f q) :=
  MorphismProperty.of_isPullback (isPullback φ f q) inferInstance

instance target_isNoetherian [IsFinite q] : IsNoetherian (target φ q) :=
  isNoetherian_of_finiteType (pullback.snd q (Spec.map (CommRingCat.ofHom φ)))

instance source_isNoetherian [IsFinite f] [IsFinite q] :
    IsNoetherian (source φ f q) :=
  isNoetherian_of_finiteType (map φ f q)

/-- The full all-branch pushforward formula, with the original generic residue degree. -/
theorem finitePushforward_fundamentalCycle [IsIntegral P] [IsIntegral Q]
    [IsFinite f] [IsFinite q] :
    IntegralCycle.finitePushforward (map φ f q) (fundamentalCycle (source φ f q)) =
      (f.residueDegree (genericPoint P) : ℤ) • fundamentalCycle (target φ q) := by
  let x := genericPoint P
  let jP := (pointClosure x).val.subschemeι
  let jQ := (pointClosure (f x)).val.subschemeι
  have hx : f x = genericPoint Q := by
    have h := mem_genericPoints_of_finite q (f x)
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h
  let : IsIso jP := genericPointClosure_isIso P
  let : IsIso jQ := by
    dsimp only [jQ]
    rw [hx]
    infer_instance
  let i := pullback.fst (f ≫ q) (Spec.map (CommRingCat.ofHom φ)) ≫ inv jP
  let g := pullback.fst q (Spec.map (CommRingCat.ofHom φ)) ≫ inv jQ
  have sq : IsPullback i (map φ f q) (pointClosureMap f x) g := by
    apply (isPullback φ f q).of_iso'
      (Iso.refl _) (asIso jP) (Iso.refl _) (asIso jQ)
    · simp [i]
    · simp
    · exact (pointClosureMap_ambient f x).symm
    · simp [g]
  have hg : ∀ w : genericPoints (source φ f q),
      map φ f q w.1 ∈ genericPoints (target φ q) := fun w =>
    mem_genericPoints_of_finite
      (pullback.snd q (Spec.map (CommRingCat.ofHom φ))) _
  have hp : ∀ y : genericPoints (target φ q),
      g y.1 = genericPoint (pointClosure (f x)).val.subscheme := by
    intro y
    have : IsFinite (jQ ≫ q) := inferInstance
    have h := mem_genericPoints_of_finite (jQ ≫ q) (g y.1)
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using h
  exact IntegralExteriorCyclePushforward.finitePushforward_fundamentalCycle_pointClosure_baseChange
    f x sq hg hp

end Motivic.FinitePointBaseChange
