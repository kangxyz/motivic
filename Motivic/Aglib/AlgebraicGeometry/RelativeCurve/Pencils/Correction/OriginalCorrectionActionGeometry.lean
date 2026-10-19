/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CorrespondenceSites
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.FactorBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionNormDiagram
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.IdentityGenericFiberNorm
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.BoundarySourceChange
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiberPullback
/-! # The actual correction diagram used by the original transfer action

The first finite map is the identity, the second is the original finite map on
the second factor. Only the target pair changes its first parameter. The original
retained target contains the graph, whereas the smaller retained target need not.
The original target boundary is infinity alone, not the marked incidence.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.OriginalPairNormBoundaryUnits`, `Pencils.NativeCorrectionTransferAction`,
`Pencils.NativeSectionPairTransferAction`, `Pencils.OriginalTargetLambda`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.Hom Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe v u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The actual restriction of the second retained factor, with the first
parameter unchanged. The factorization equality is an equality of scheme maps. -/
def retainedSubopenMap {S C A U V : Scheme.{u}} (b : A ⟶ S) (π : C ⟶ S)
    (j : U ⟶ C) (v : V ⟶ C) (r : V ⟶ U) (hr : r ≫ j = v) :
    retainedProduct b π v ⟶ retainedProduct b π j :=
  pullback.lift (pullback.fst b (v ≫ π)) (pullback.snd b (v ≫ π) ≫ r) (by
    rw [Category.assoc, ← Category.assoc r j π, hr]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem retainedSubopenMap_fst {S C A U V : Scheme.{u}} (b : A ⟶ S) (π : C ⟶ S)
    (j : U ⟶ C) (v : V ⟶ C) (r : V ⟶ U) (hr : r ≫ j = v) :
    retainedSubopenMap b π j v r hr ≫ pullback.fst b (j ≫ π) =
      pullback.fst b (v ≫ π) := by
  simp [retainedSubopenMap]

@[reassoc (attr := simp)]
theorem retainedSubopenMap_snd {S C A U V : Scheme.{u}} (b : A ⟶ S) (π : C ⟶ S)
    (j : U ⟶ C) (v : V ⟶ C) (r : V ⟶ U) (hr : r ≫ j = v) :
    retainedSubopenMap b π j v r hr ≫ pullback.snd b (j ≫ π) =
      pullback.snd b (v ≫ π) ≫ r := by
  simp [retainedSubopenMap]

/-- The restriction is the same compactification map, not a replacement open. -/
theorem retainedSubopenMap_inclusion {S C A U V : Scheme.{u}}
    (b : A ⟶ S) (π : C ⟶ S) (j : U ⟶ C) (v : V ⟶ C)
    (r : V ⟶ U) (hr : r ≫ j = v) :
    retainedSubopenMap b π j v r hr ≫ retainedProductInclusion b π j =
      retainedProductInclusion b π v := by
  apply pullback.hom_ext <;> simp [Category.assoc, hr]

/-- Infinity alone covers the complement of the original large retained curve. -/
theorem retainedProduct_infinity_cover {S C A U D : Scheme.{u}}
    (b : A ⟶ S) (π : C ⟶ S) (j : U ⟶ C) (d : D ⟶ C)
    (hc : (Set.range j)ᶜ ⊆ Set.range d) :
    ∀ x : (pullback b π : Scheme.{u}),
      x ∈ Set.range (retainedProductInclusion b π j) ∨
        x ∈ Set.range (pullback.fst (pullback.snd b π) d) := by
  intro x
  rw [Scheme.range_snd_eq_preimage_of_isPullback _ _ _ _
    (retainedProductInclusion_isPullback b π j), Scheme.Pullback.range_fst]
  exact or_iff_not_imp_left.mpr (fun hx => hc hx)

/-- The marked section is already retained in the large curve. A small curve
factoring through it therefore gives the required infinity-only cover. -/
theorem retained_complement_subset_infinity {C Y V Z D : Scheme.{u}}
    (j : Y ⟶ C) (v : V ⟶ C) (r : V ⟶ Y) (hr : r ≫ j = v)
    (s : Z ⟶ Y) (d : D ⟶ C)
    (hc : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j)) :
    (Set.range j)ᶜ ⊆ Set.range d := by
  intro x hx
  rcases hc x with ⟨y, hy⟩ | hd | ⟨z, hz⟩
  · exact (hx ⟨r y, (congrArg (fun f => f y) hr).trans hy⟩).elim
  · exact hd
  · exact (hx ⟨s z, hz⟩).elim

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- The identity leg of the actual correction comparison is free on every
affine chart, through its own rank-one scalar algebra. -/
theorem identity_exists_free_affine_neighborhood {T : Scheme.{u}} (x : T) :
    ∃ (W : T.Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (let : Algebra Γ(T, W) Γ(pullback (𝟙 T) hW.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (𝟙 T) hW.fromSpec)).toAlgebra
       Module.Free Γ(T, W) Γ(pullback (𝟙 T) hW.fromSpec, ⊤)) := by
  obtain ⟨W, hW, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : T.Opens) from trivial)
  refine ⟨W, hW, hx, ?_⟩
  let : Algebra Γ(T, W) Γ(pullback (𝟙 T) hW.fromSpec, ⊤) :=
    (scalarMap (pullback.snd (𝟙 T) hW.fromSpec)).toAlgebra
  exact Module.Free.of_equiv (scalarEquivOfIsIso
    (pullback.snd (𝟙 T) hW.fromSpec)).toLinearEquiv

end AlgebraicGeometry.FiniteSchemeNormBaseChange

namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y A D DA : Scheme.{u}} (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (j : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (hret : j ≫ f = p ≫ jA)
  (hA : jA ≫ π = q) (a : A ⟶ X) (d : D ⟶ C) (dA : DA ⟶ P)

/-- The two original infinity schemes, including their full scheme structures. -/
def originalCorrectionPairInfinity : Fin 2 → Scheme.{u} :=
  ![pullback (pullback.snd (jA ≫ π) π) dA,
    pullback (pullback.snd (a ≫ q) (f ≫ π)) d]

/-- The infinity schemes after the one genuine first-parameter change. -/
def originalCorrectionPairChangedInfinity : Fin 2 → Scheme.{u} :=
  ![pullback (pullback.snd (a ≫ q) π) dA,
    pullback (pullback.snd (a ≫ q) (f ≫ π)) d]

/-- The original comparison uses infinity-only boundaries in both large curves. -/
def originalCorrectionPairInfinityInclusion : ∀ i,
    originalCorrectionPairInfinity q π f jA a d dA i ⟶
      originalCorrectionPairCompact q π f jA a i :=
  Fin.twoCases (pullback.fst _ dA) (pullback.fst _ d)

/-- The same infinity inclusions over the punctured parameter. -/
def originalCorrectionPairChangedInfinityInclusion : ∀ i,
    originalCorrectionPairChangedInfinity q π f a d dA i ⟶
      originalCorrectionPairChangedCompact q π f a i :=
  Fin.twoCases (pullback.fst _ dA) (pullback.fst _ d)

/-- Actual base change on infinity keeps every point and nilpotent in the fiber. -/
def originalCorrectionPairInfinityMap : ∀ i,
    originalCorrectionPairChangedInfinity q π f a d dA i ⟶
      originalCorrectionPairInfinity q π f jA a d dA i :=
  Fin.twoCases (constantInfinitySourceMap a (jA ≫ π) π (a ≫ q)
    (congrArg (fun k => a ≫ k) hA.symm) dA) (𝟙 _)

/-- This literal equality transports the original infinity functional units. -/
theorem originalCorrectionPairInfinityMap_inclusion (i : Fin 2) :
    originalCorrectionPairInfinityMap q π f jA hA a d dA i ≫
        originalCorrectionPairInfinityInclusion q π f jA a d dA i =
      originalCorrectionPairChangedInfinityInclusion q π f a d dA i ≫
        originalCorrectionPairCompactMap q π f jA hA a i := by
  fin_cases i
  · exact constantInfinitySourceMap_fst a (jA ≫ π) π (a ≫ q)
      (congrArg (fun k => a ≫ k) hA.symm) dA
  · simp [originalCorrectionPairInfinityMap, originalCorrectionPairInfinityInclusion,
      originalCorrectionPairChangedInfinityInclusion, originalCorrectionPairCompactMap]

/-- The actual identity and finite-map legs have free charts from the original
finite map alone. No freeness of a marked or residual summand is asserted. -/
theorem originalCorrectionPairFiniteMap_free [IsFinite f]
    {ι : Type u} (R : ι → CommRingCat.{u}) (w : ∀ i, Spec (R i) ⟶ P)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (R i) Γ(pullback f (w i), ⊤) :=
        (scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (R i) Γ(pullback f (w i), ⊤))
    (i : Fin 2) (x : (pullback (a ≫ q) π : Scheme.{u})) :
    ∃ (W : (pullback (a ≫ q) π).Opens) (hW : IsAffineOpen W), x ∈ W ∧
      (let : Algebra Γ(pullback (a ≫ q) π, W)
          Γ(pullback (originalCorrectionPairFiniteMap q π f a i) hW.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (originalCorrectionPairFiniteMap q π f a i)
          hW.fromSpec)).toAlgebra
       Module.Free Γ(pullback (a ≫ q) π, W)
         Γ(pullback (originalCorrectionPairFiniteMap q π f a i) hW.fromSpec, ⊤)) := by
  fin_cases i
  · exact identity_exists_free_affine_neighborhood x
  · exact normProductMap_exists_free_affine_neighborhood π f (a ≫ q) R w hcover hfree x

/-- The actual original graph lies in the large retained target. -/
def originalCorrectionRetainedGraph : X ⟶ retainedProduct (jA ≫ π) π jA :=
  pullback.lift (𝟙 X) (𝟙 X) rfl

theorem originalCorrectionRetainedGraph_inclusion :
    originalCorrectionRetainedGraph π jA ≫ retainedProductInclusion (jA ≫ π) π jA =
      compactificationGraph π jA := by
  apply pullback.hom_ext <;> simp [originalCorrectionRetainedGraph, compactificationGraph]

@[reassoc (attr := simp)]
theorem originalCorrectionRetainedGraph_snd :
    originalCorrectionRetainedGraph π jA ≫ pullback.snd (jA ≫ π) (jA ≫ π) = 𝟙 X := by
  simp [originalCorrectionRetainedGraph]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {S C P X Y A U V : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine U] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [Smooth q] (π : P ⟶ S) (f : C ⟶ P)
  (j : Y ⟶ C) [Smooth (j ≫ (f ≫ π))]
  (jA : X ⟶ P) [Smooth (jA ≫ π)]
  (p : Y ⟶ X) (hret : j ≫ f = p ≫ jA) (hA : jA ≫ π = q)
  (a : A ⟶ X) [Smooth a] (u : U ⟶ X) [Smooth ((u ≫ jA) ≫ π)]
  (v : V ⟶ C) [Smooth (v ≫ (f ≫ π))]
  (vY : V ⟶ Y) (hvY : vY ≫ j = v) (pV : V ⟶ U) (hpV : pV ≫ u = vY ≫ p)

omit [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine U] [IsAffine V]
  [Smooth t] [Smooth (j ≫ (f ≫ π))] [Smooth (jA ≫ π)]
  [Smooth ((u ≫ jA) ≫ π)] [Smooth (v ≫ (f ≫ π))] in
include hvY hpV hret in
/-- The actual small-source map is a map over the same original base. -/
theorem correctionSmallTarget_structure :
    pV ≫ (((u ≫ jA) ≫ π) ≫ t) = (v ≫ (f ≫ π)) ≫ t := by
  have hf : (pV ≫ u) ≫ jA = v ≫ f := by
    rw [hpV, Category.assoc, ← hret, ← Category.assoc, hvY]
  simpa only [Category.assoc] using congrArg (fun w => w ≫ π ≫ t) hf

/-- The actual small-source map on smooth sites, with no correspondence or
presheaf identity included in its data. -/
def correctionSmallTargetMap : relativeTargetSite k t (f ≫ π) v ⟶
    relativeTargetSite k t π (u ≫ jA) :=
  SmoothSite.homMk pV (correctionSmallTarget_structure t π f j jA p hret
    u v vY hvY pV hpV)

omit [IsAffine S] [IsAffine X] [IsAffine A] [IsAffine U]
  [Smooth t] [Smooth q] [Smooth (jA ≫ π)] [Smooth a]
  [Smooth ((u ≫ jA) ≫ π)] in
include hA in
theorem correctionSmallParameter_structure (r : A ⟶ U) (hr : r ≫ u = a) :
    r ≫ (((u ≫ jA) ≫ π) ≫ t) = (a ≫ q) ≫ t := by
  calc
    _ = (r ≫ u) ≫ ((jA ≫ π) ≫ t) := by simp only [Category.assoc]
    _ = (a ≫ q) ≫ t := by rw [hr, hA, Category.assoc]

/-- The graph term has the actual factorization of a through the target puncture. -/
def correctionSmallParameterMap (r : A ⟶ U) (hr : r ≫ u = a) :
    psiSourceSite k t q a ⟶ relativeTargetSite k t π (u ≫ jA) :=
  SmoothSite.homMk r (correctionSmallParameter_structure t q π jA hA a u r hr)

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The two projections give the same structure map on the literal retained
product. This proof does not identify or shrink either parameter. -/
theorem retainedProduct_structure {S C A V K : Scheme.{u}}
    (b : A ⟶ S) (π : C ⟶ S) (v : V ⟶ C) (t : S ⟶ K) :
    (retainedProductInclusion b π v ≫ pullback.fst b π) ≫ (b ≫ t) =
      pullback.snd b (v ≫ π) ≫ ((v ≫ π) ≫ t) := by
  rw [retainedProductInclusion_fst, ← Category.assoc, pullback.condition]
  simp only [Category.assoc]

/-- The actual second-factor map transports the retained product structure
without changing either section or correspondence. -/
theorem retainedProduct_structure_factor {S C A V K Q : Scheme.{u}}
    (b : A ⟶ S) (π : C ⟶ S) (v : V ⟶ C) (t : S ⟶ K)
    (g : V ⟶ Q) (qQ : Q ⟶ K) (hg : g ≫ qQ = (v ≫ π) ≫ t) :
    (retainedProductInclusion b π v ≫ pullback.fst b π) ≫ (b ≫ t) =
      (pullback.snd b (v ≫ π) ≫ g) ≫ qQ := by
  rw [Category.assoc (pullback.snd b (v ≫ π)) g qQ, hg]
  exact retainedProduct_structure b π v t

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {k : Type u} [Field k] {S P X A : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine A]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [Smooth q] (π : P ⟶ S) (j : X ⟶ P) [Smooth (j ≫ π)]
  (hA : j ≫ π = q) (a : A ⟶ X) [Smooth a]

instance (i : Fin 2) : IsAffine (originalCorrectionPairParameter X A i) := by
  fin_cases i
  · change IsAffine X
    infer_instance
  · change IsAffine A
    infer_instance

/-- Structure maps are defined on the same dependent parameter family as the
actual compactification diagram, so its underlying schemes are literal. -/
def originalCorrectionPairStructureMap : ∀ i,
    originalCorrectionPairParameter X A i ⟶ Spec (.of k) :=
  Fin.twoCases ((j ≫ π) ≫ t) ((a ≫ q) ≫ t)

instance (i : Fin 2) : Smooth (originalCorrectionPairStructureMap t q π j a i) := by
  fin_cases i <;>
    simp only [originalCorrectionPairStructureMap, Fin.twoCases_mk_zero,
      Fin.twoCases_mk_one] <;>
    infer_instance

/-- The two original parameter sites are the target and the punctured parameter. -/
def originalCorrectionPairSite (i : Fin 2) : SmoothSite (Spec (.of k)) :=
  SmoothSite.mk (originalCorrectionPairStructureMap t q π j a i)

instance (i : Fin 2) : IsAffine (originalCorrectionPairSite t q π j a i).left :=
  inferInstanceAs (IsAffine (originalCorrectionPairParameter X A i))

omit [IsAffine S] [IsAffine X] [IsAffine A] [Smooth t] [Smooth q]
  [Smooth (j ≫ π)] [Smooth a] in
include hA in
theorem originalCorrectionPairParameterMap_structure (i : Fin 2) :
    originalCorrectionPairParameterMap a i ≫
        originalCorrectionPairStructureMap t q π j a i = (a ≫ q) ≫ t := by
  fin_cases i <;> simp [originalCorrectionPairParameterMap,
    originalCorrectionPairStructureMap, Category.assoc, hA]

/-- The maps of smooth sites are exactly a and identity. In particular no lift
of a to the finite cover is part of the construction. -/
def originalCorrectionPairSiteMap (i : Fin 2) :
    psiSourceSite k t q a ⟶ originalCorrectionPairSite t q π j a i :=
  SmoothSite.homMk (originalCorrectionPairParameterMap a i)
    (originalCorrectionPairParameterMap_structure t q π j hA a i)

instance [Flat a] (i : Fin 2) : Flat (originalCorrectionPairSiteMap t q π j hA a i).left := by
  fin_cases i
  · change Flat a
    infer_instance
  · change Flat (𝟙 A)
    infer_instance

end AlgebraicGeometry.Scheme.RelativeCurvePencil

namespace AlgebraicGeometry.Scheme.Hom

variable {S C P X Y A : Scheme.{u}} (q : X ⟶ S) (π : P ⟶ S) (f : C ⟶ P)
  (j : Y ⟶ C) (jA : X ⟶ P) (p : Y ⟶ X) (hret : j ≫ f = p ≫ jA)
  (a : A ⟶ X)

/-- The large target maps are the actual second projection and the original
cover map, respectively. -/
def originalCorrectionPairTargetMap : ∀ i,
    originalCorrectionPairRetained q π f j jA a i ⟶ X :=
  Fin.twoCases (pullback.snd (jA ≫ π) (jA ≫ π)) (pullback.snd (a ≫ q) (j ≫ (f ≫ π)) ≫ p)

/-- The same large target maps commute with the first-parameter change and
the second-factor finite map. -/
theorem originalCorrectionPairRetainedMap_target (hA : jA ≫ π = q) (i : Fin 2) :
    originalCorrectionPairRetainedMap q π f j jA hA a i ≫
        originalCorrectionPairTargetMap q π f j jA p a i =
      originalCorrectionPairRetainedFiniteMap q π f j jA p hret a i ≫
        pullback.snd (a ≫ q) (jA ≫ π) := by
  fin_cases i
  · simp [originalCorrectionPairRetainedMap, originalCorrectionPairTargetMap,
      originalCorrectionPairRetainedFiniteMap, retainedParameterChangeMap]
  · simp [originalCorrectionPairRetainedMap, originalCorrectionPairTargetMap,
      originalCorrectionPairRetainedFiniteMap]

section Small
variable {U V : Scheme.{u}} (u : U ⟶ X) (v : V ⟶ C) (vY : V ⟶ Y)
  (hvY : vY ≫ j = v) (pV : V ⟶ U) (hpV : pV ≫ u = vY ≫ p)

/-- The two small retained curves are formed with the actual target puncture
and the chosen small source; the original marked section is not required in V. -/
def originalCorrectionPairSmallRetained : Fin 2 → Scheme.{u} :=
  ![retainedProduct (jA ≫ π) π (u ≫ jA), retainedProduct (a ≫ q) (f ≫ π) v]

/-- Include both small retained curves in their original compactifications. -/
def originalCorrectionPairSmallInclusion : ∀ i,
    originalCorrectionPairSmallRetained q π f jA a u v i ⟶
      originalCorrectionPairCompact q π f jA a i :=
  Fin.twoCases (retainedProductInclusion (jA ≫ π) π (u ≫ jA))
    (retainedProductInclusion (a ≫ q) (f ≫ π) v)

/-- Restrict only the second factors of the original retained curves. -/
def originalCorrectionPairSmallMap : ∀ i,
    originalCorrectionPairSmallRetained q π f jA a u v i ⟶
      originalCorrectionPairRetained q π f j jA a i :=
  Fin.twoCases (retainedSubopenMap (jA ≫ π) π jA (u ≫ jA) u rfl)
    (retainedSubopenMap (a ≫ q) (f ≫ π) j v vY hvY)

theorem originalCorrectionPairSmallMap_inclusion (i : Fin 2) :
    originalCorrectionPairSmallMap q π f j jA a u v vY hvY i ≫
        originalCorrectionPairRetainedInclusion q π f j jA a i =
      originalCorrectionPairSmallInclusion q π f jA a u v i := by
  fin_cases i
  · exact retainedSubopenMap_inclusion (jA ≫ π) π jA (u ≫ jA) u rfl
  · exact retainedSubopenMap_inclusion (a ≫ q) (f ≫ π) j v vY hvY

/-- On the small curves the second projection and pV have the actual small
target U, rather than an auxiliary target chosen from the boundary values. -/
def originalCorrectionPairSmallTargetMap : ∀ i,
    originalCorrectionPairSmallRetained q π f jA a u v i ⟶ U :=
  Fin.twoCases (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV)

include hpV in
theorem originalCorrectionPairSmallTargetMap_comp (i : Fin 2) :
    originalCorrectionPairSmallTargetMap q π f jA a u v pV i ≫ u =
      originalCorrectionPairSmallMap q π f j jA a u v vY hvY i ≫
        originalCorrectionPairTargetMap q π f j jA p a i := by
  fin_cases i
  · simp [originalCorrectionPairSmallTargetMap, originalCorrectionPairSmallMap,
      originalCorrectionPairTargetMap]
  · simp [originalCorrectionPairSmallTargetMap, originalCorrectionPairSmallMap,
      originalCorrectionPairTargetMap, Category.assoc, hpV]

instance [IsOpenImmersion jA] [IsOpenImmersion u] [IsOpenImmersion v] (i : Fin 2) :
    IsOpenImmersion (originalCorrectionPairSmallInclusion q π f jA a u v i) := by
  fin_cases i <;>
    simp only [originalCorrectionPairSmallInclusion, Fin.twoCases_mk_zero,
      Fin.twoCases_mk_one] <;>
    infer_instance

instance [IsAffine S] [IsAffine X] [IsAffine A] [IsAffine U] [IsAffine V] (i : Fin 2) :
    IsAffine (originalCorrectionPairSmallRetained q π f jA a u v i) := by
  fin_cases i
  · exact retainedProduct_affine (jA ≫ π) π (u ≫ jA)
  · exact retainedProduct_affine (a ≫ q) (f ≫ π) v

instance [SmoothOfRelativeDimension 1 ((u ≫ jA) ≫ π)]
    [SmoothOfRelativeDimension 1 (v ≫ (f ≫ π))] (i : Fin 2) :
    SmoothOfRelativeDimension 1 (originalCorrectionPairSmallInclusion q π f jA a u v i ≫
      originalCorrectionPairProjection q π f jA a i) := by
  fin_cases i
  · exact retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
  · exact retainedProduct_smooth (a ≫ q) (f ≫ π) v

end Small

variable {D DA Z U V : Scheme.{u}} (d : D ⟶ C) (dA : DA ⟶ P)
  (z : Z ⟶ X) (s : Z ⟶ Y)
  (hq : j ≫ (f ≫ π) = p ≫ q) (hs : s ≫ p = z)
  (u : U ⟶ X) (v : V ⟶ C)

/-- The smaller action boundary is the full original marked-plus-infinity
boundary. It is different from the infinity-only large comparison boundary. -/
def originalCorrectionPairFullBoundary : Fin 2 → Scheme.{u} :=
  ![pullback (pullback.snd (jA ≫ π) π) dA ⨿ pullback (jA ≫ π) (z ≫ jA ≫ π),
    pullback (pullback.snd (a ≫ q) (f ≫ π)) d ⨿ pullback (a ≫ q) (z ≫ q)]

/-- Map the full marked-plus-infinity boundary into each original compactification. -/
def originalCorrectionPairFullBoundaryInclusion : ∀ i,
    originalCorrectionPairFullBoundary q π f jA a d dA z i ⟶
      originalCorrectionPairCompact q π f jA a i :=
  Fin.twoCases (fullBoundaryProductMap π jA dA z)
    (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)

/-- The actual smaller source cover induces an infinity-only cover on the
original retained source, since the marked section is retained there. -/
theorem originalCorrectionPair_infinity_cover
    (vY : V ⟶ Y) (hvY : vY ≫ j = v)
    (hinfty : (Set.range jA)ᶜ ⊆ Set.range dA)
    (hcover : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
    (i : Fin 2) (x : originalCorrectionPairCompact q π f jA a i) :
    x ∈ Set.range (originalCorrectionPairRetainedInclusion q π f j jA a i) ∨
      x ∈ Set.range (originalCorrectionPairInfinityInclusion q π f jA a d dA i) := by
  fin_cases i
  · exact retainedProduct_infinity_cover (jA ≫ π) π jA dA hinfty x
  · exact retainedProduct_infinity_cover (a ≫ q) (f ≫ π) j d
      (retained_complement_subset_infinity j v vY hvY s d hcover) x

/-- The changed large curves have the same infinity-only cover. -/
theorem originalCorrectionPair_changedInfinity_cover
    (vY : V ⟶ Y) (hvY : vY ≫ j = v)
    (hinfty : (Set.range jA)ᶜ ⊆ Set.range dA)
    (hcover : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
    (i : Fin 2) (x : originalCorrectionPairChangedCompact q π f a i) :
    x ∈ Set.range (originalCorrectionPairChangedInclusion q π f j jA a i) ∨
      x ∈ Set.range (originalCorrectionPairChangedInfinityInclusion q π f a d dA i) := by
  fin_cases i
  · exact retainedProduct_infinity_cover (a ≫ q) π jA dA hinfty x
  · exact retainedProduct_infinity_cover (a ≫ q) (f ≫ π) j d
      (retained_complement_subset_infinity j v vY hvY s d hcover) x

/-- The marked puncture and infinity cover precisely what the smaller retained
target omits. This is only a support statement, not a value-one assumption. -/
theorem correction_target_small_cover
    (hinfty : (Set.range jA)ᶜ ⊆ Set.range dA)
    (hpuncture : (Set.range u)ᶜ ⊆ Set.range z) (x : P) :
    x ∈ Set.range (u ≫ jA) ∨ x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ jA) := by
  by_cases hx : x ∈ Set.range jA
  · obtain ⟨y, rfl⟩ := hx
    by_cases hy : y ∈ Set.range u
    · obtain ⟨w, rfl⟩ := hy
      exact Or.inl ⟨w, rfl⟩
    · obtain ⟨w, hw⟩ := hpuncture hy
      exact Or.inr (Or.inr ⟨w, congrArg jA hw⟩)
  · exact Or.inr (Or.inl (hinfty hx))

theorem originalCorrectionPair_fullBoundary_cover
    (hinfty : (Set.range jA)ᶜ ⊆ Set.range dA)
    (hpuncture : (Set.range u)ᶜ ⊆ Set.range z)
    (hcover : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
    (i : Fin 2) (x : originalCorrectionPairCompact q π f jA a i) :
    x ∈ Set.range (originalCorrectionPairSmallInclusion q π f jA a u v i) ∨
      x ∈ Set.range
        (originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs i) := by
  fin_cases i
  · exact lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture) x
  · exact psiBoundary_retained_cover q (f ≫ π) j p hq a z s hs d v hcover x

end AlgebraicGeometry.Scheme.Hom
