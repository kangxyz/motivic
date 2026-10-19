/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ResidueField.FiniteFieldResidueDegree
public import Motivic.Aglib.AlgebraicGeometry.Cycles.BaseChange.CyclePushforward
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Fundamental cycles under a finite scalar projection

The whole scalar-extended support is retained, with every generic local length.
The degree comes from the complete degree-length identity, including inseparable
and nonreduced scalar extensions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange _root_.AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme

private theorem pointClosure_genericPoint_ideal (X : Scheme.{u}) [IsIntegral X] :
    (pointClosure (genericPoint X)).val = ⊥ := by
  change (Scheme.IdealSheafData.vanishingIdeal
    ⟨closure {genericPoint X}, isClosed_closure⟩).radical = ⊥
  have ht : (⟨closure {genericPoint X}, isClosed_closure⟩ : TopologicalSpace.Closeds X) = ⊤ := by
    apply SetLike.coe_injective
    exact (genericPoint_spec X).def
  rw [ht, Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.nilradical_eq_bot, Scheme.IdealSheafData.radical_bot,
    Scheme.nilradical_eq_bot]

private instance pointClosure_genericPoint_isIso (X : Scheme.{u}) [IsIntegral X] :
    IsIso (pointClosure (genericPoint X)).val.subschemeι := by
  rw [Scheme.isIso_subschemeι_iff_eq_bot]
  exact pointClosure_genericPoint_ideal X

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

local instance scalarMap_isFinite :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

local instance scalarPullback_isNoetherian
    {X : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Spec (.of k)) :
    IsNoetherian (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k E)))) :=
  isNoetherian_of_finiteType (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E))))

/-- The whole finite scalar fiber has total degree `[E : k]`, with all lengths. -/
theorem finitePushforward_scalar_fundamentalCycle
    {X : Scheme.{u}} [IsNoetherian X] (p : X ⟶ Spec (.of k)) :
    IntegralCycle.finitePushforward
        (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k E))))
      (fundamentalCycle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k E))))) =
      (Module.finrank k E : ℤ) • fundamentalCycle X := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k E))
  let x := genericPoint (Spec (.of E))
  let jE := (pointClosure x).val.subschemeι
  let jk := (pointClosure (f x)).val.subschemeι
  have hx : f x = genericPoint (Spec (.of k)) := Subsingleton.elim _ _
  let : IsIso jE := pointClosure_genericPoint_isIso (Spec (.of E))
  let : IsIso jk := by
    dsimp only [jk]
    rw [hx]
    infer_instance
  let i := pullback.snd p f ≫ inv jE
  let g := p ≫ inv jk
  have sq : IsPullback i (pullback.fst p f) (pointClosureMap f x) g := by
    apply (IsPullback.of_hasPullback p f).flip.of_iso'
      (Iso.refl _) (asIso jE) (Iso.refl _) (asIso jk)
    · simp [i]
    · simp
    · exact (pointClosureMap_ambient f x).symm
    · simp [g]
  have : Flat f := Flat.SpecMap_iff.mpr
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k E))
  have hg : ∀ w : genericPoints (pullback p f : Scheme),
      pullback.fst p f w.1 ∈ genericPoints X := fun w =>
    mem_genericPoints_of_generalizing (pullback.fst p f)
      (Flat.generalizingMap _) w.1 w.2
  have hp : ∀ y : genericPoints X,
      g y.1 = genericPoint (pointClosure (f x)).val.subscheme := by
    intro y
    apply jk.homeomorph.injective
    exact Subsingleton.elim _ _
  have h :=
    Pushforward.finitePushforward_fundamentalCycle_pointClosure_baseChange
      f x sq hg hp
  rw [Scheme.Hom.residueDegree_SpecMap_algebraMap] at h
  exact h

end AlgebraicGeometry.Scheme
