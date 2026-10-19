/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.FiniteCovers
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.Sites.Coverage

/-!
# Finite-coproduct descent for ordinary Nisnevich sheaves

For a presheaf of types taking actual finite disjoint unions to products by
component restriction, the ordinary Nisnevich sheaf condition is equivalent to
descent for genuine singleton Nisnevich covers. Every target is explicitly
assumed Noetherian. The product hypothesis includes the empty disjoint union.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- Restriction to the components of the actual finite disjoint union. -/
def finiteCoproductRestriction (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
    {n : ℕ} (Y : Fin n → SmoothSite S) :
    P.obj (op (finiteCoproduct Y)) → ∀ i, P.obj (op (Y i)) :=
  fun s i => P.map (finiteCoproductι Y i).op s

/-- The components of the actual finite disjoint union form a Nisnevich family. -/
theorem finiteCoproductι_mem_nisnevichPrecoverage {n : ℕ}
    (Y : Fin n → SmoothSite S) :
    Presieve.ofArrows Y (finiteCoproductι Y) ∈ nisnevichPrecoverage S (finiteCoproduct Y) := by
  rw [ofArrows_mem_nisnevichPrecoverage_iff]
  refine ⟨fun i => inferInstance, fun z => ?_⟩
  obtain ⟨i, y, hy⟩ := finiteCoproduct_covers Y z
  exact ⟨i, y, hy, inferInstance⟩

/-- The normalized total map is a genuine cover in the smooth site. -/
theorem FiniteNisnevichCoverNormalization.mem_nisnevichPrecoverage
    {X : SmoothSite S} {ι : Type w} {Y : ι → SmoothSite S} {f : ∀ i, Y i ⟶ X}
    (N : FiniteNisnevichCoverNormalization f) :
    Presieve.singleton N.map ∈ nisnevichPrecoverage S X := by
  rw [mem_nisnevichPrecoverage_iff, Presieve.map_singleton]
  exact N.mem_precoverage

/-- A pullback family of a smooth Nisnevich family is again covering. -/
theorem nisnevich_pullback_family {X Z : SmoothSite S} {ι : Type w}
    {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X) [∀ i, Etale (f i).left]
    (hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X) (g : Z ⟶ X) :
    Presieve.ofArrows (fun i => pullback (f i) g) (fun i => pullback.snd (f i) g) ∈
      nisnevichPrecoverage S Z :=
  Precoverage.mem_coverings_of_isPullback f hf g _ _
    (fun i => (IsPullback.of_hasPullback (f i) g).flip)

/-- Base change of a genuine singleton Nisnevich cover is genuine. -/
theorem nisnevich_pullback_singleton {X Y Z : SmoothSite S} (q : Y ⟶ X)
    [Etale q.left] (hq : Presieve.singleton q ∈ nisnevichPrecoverage S X) (g : Z ⟶ X) :
    Presieve.singleton (pullback.snd q g) ∈ nisnevichPrecoverage S Z := by
  let := (nisnevichPrecoverage S).hasPullbacks_of_mem g hq
  simpa only [Presieve.pullback_singleton] using Precoverage.pullbackArrows_mem g hq

variable (P : (SmoothSite S)ᵒᵖ ⥤ Type v)
variable (hprod : ∀ (n : ℕ) (Y : Fin n → SmoothSite S),
  Function.Bijective (finiteCoproductRestriction P Y))
variable (hsingle : ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
  Presieve.singleton q ∈ nisnevichPrecoverage S X → Presieve.IsSheafFor P (.singleton q))

include hprod hsingle

/-- Singleton descent and finite-product injectivity give separation for every
Nisnevich family over a Noetherian target. -/
theorem sections_ext_of_nisnevich_family {X : SmoothSite S} [IsNoetherian X.left]
    {ι : Type w} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X)
    {s t : P.obj (op X)} (h : ∀ i, P.map (f i).op s = P.map (f i).op t) : s = t := by
  have hf' : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left := by
    exact (Nisnevich.ofArrows_mem_precoverage_iff _).mpr
      ((ofArrows_mem_nisnevichPrecoverage_iff f).mp hf)
  let N := normalizeFiniteNisnevichCoverOfMem f hf'
  apply (Presieve.isSeparatedFor_singleton.mp
    (hsingle N.map N.mem_nisnevichPrecoverage).isSeparatedFor)
  apply (hprod N.size _).injective
  funext i
  change P.map (N.inclusion i).op (P.map N.map.op s) =
    P.map (N.inclusion i).op (P.map N.map.op t)
  simpa only [← Functor.map_comp_apply, ← op_comp, N.inclusion_map] using h (N.index i)

/-- A section on a finite total space with compatible component values restricts
correctly along every map into that total space lying over an original member. -/
private theorem restriction_eq_of_component_values
    {X : SmoothSite S} {ι : Type w} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    {n : ℕ} (a : Fin n → ι) (x : ∀ i, P.obj (op (Y i)))
    (hx : Presieve.Arrows.Compatible P f x)
    (s : P.obj (op (finiteCoproduct (fun j => Y (a j)))))
    (hs : ∀ j, P.map (finiteCoproductι (fun k => Y (a k)) j).op s = x (a j))
    {Z : SmoothSite S} [IsNoetherian Z.left]
    (g : Z ⟶ finiteCoproduct (fun j => Y (a j))) (i : ι) (h : Z ⟶ Y i)
    (e : g ≫ finiteCoproductDesc (fun j => f (a j)) = h ≫ f i) :
    P.map g.op s = P.map h.op (x i) := by
  let incl := finiteCoproductι (fun j => Y (a j))
  apply sections_ext_of_nisnevich_family P hprod hsingle
    (fun j => pullback.snd (incl j) g)
    (nisnevich_pullback_family incl (finiteCoproductι_mem_nisnevichPrecoverage _) g)
  intro j
  calc
    P.map (pullback.snd (incl j) g).op (P.map g.op s) =
        P.map (pullback.fst (incl j) g).op (P.map (incl j).op s) := by
      simp only [← Functor.map_comp_apply, ← op_comp, pullback.condition]
    _ = P.map (pullback.fst (incl j) g).op (x (a j)) := by rw [hs j]
    _ = P.map (pullback.snd (incl j) g ≫ h).op (x i) := by
      apply hx
      rw [Category.assoc, ← e, ← Category.assoc, ← pullback.condition,
        Category.assoc, finiteCoproductι_desc]
    _ = P.map (pullback.snd (incl j) g).op (P.map h.op (x i)) := by
      simp only [op_comp, Functor.map_comp_apply]

variable [∀ X : SmoothSite S, IsNoetherian X.left]

/-- Finite-product preservation and genuine singleton descent imply descent for
an arbitrary-index genuine Nisnevich family. -/
theorem isSheafFor_nisnevich_family_of_finiteCoproduct
    {X : SmoothSite S} {ι : Type w} {Y : ι → SmoothSite S} (f : ∀ i, Y i ⟶ X)
    (hf : Presieve.ofArrows Y f ∈ nisnevichPrecoverage S X) :
    Presieve.IsSheafFor P (Presieve.ofArrows Y f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hf' : Presieve.ofArrows (fun i => (Y i).left) (fun i => (f i).left) ∈
      Nisnevich.precoverage X.left :=
    (Nisnevich.ofArrows_mem_precoverage_iff _).mpr
      ((ofArrows_mem_nisnevichPrecoverage_iff f).mp hf)
  let N := normalizeFiniteNisnevichCoverOfMem f hf'
  obtain ⟨s, hs⟩ := (hprod N.size (fun i => Y (N.index i))).surjective
    (fun i => x (N.index i))
  have hs' (i : Fin N.size) : P.map (N.inclusion i).op s = x (N.index i) :=
    congrFun hs i
  have hcompat : ∀ {Z : SmoothSite S} (p₁ p₂ : Z ⟶ N.total),
      p₁ ≫ N.map = p₂ ≫ N.map → P.map p₁.op s = P.map p₂.op s := by
    intro Z p₁ p₂ he
    apply sections_ext_of_nisnevich_family P hprod hsingle
      (fun i => pullback.snd (N.inclusion i) p₁)
      (nisnevich_pullback_family N.inclusion (finiteCoproductι_mem_nisnevichPrecoverage _) p₁)
    intro i
    calc
      P.map (pullback.snd (N.inclusion i) p₁).op (P.map p₁.op s) =
          P.map (pullback.fst (N.inclusion i) p₁).op (x (N.index i)) := by
        rw [← hs' i]
        simp only [← Functor.map_comp_apply, ← op_comp, pullback.condition]
      _ = P.map (pullback.snd (N.inclusion i) p₁ ≫ p₂).op s := by
        symm
        apply restriction_eq_of_component_values P hprod hsingle f N.index x hx s hs'
        rw [Category.assoc, ← he, ← Category.assoc, ← pullback.condition,
          Category.assoc, N.inclusion_map]
      _ = P.map (pullback.snd (N.inclusion i) p₁).op (P.map p₂.op s) := by
        simp only [op_comp, Functor.map_comp_apply]
  obtain ⟨t, ht, _⟩ := Presieve.isSheafFor_singleton.mp
    (hsingle N.map N.mem_nisnevichPrecoverage) s hcompat
  refine ⟨t, ?_, ?_⟩
  · intro i
    apply Presieve.isSeparatedFor_singleton.mp
      (hsingle (pullback.snd N.map (f i))
        (nisnevich_pullback_singleton N.map N.mem_nisnevichPrecoverage (f i))).isSeparatedFor
    calc
      P.map (pullback.snd N.map (f i)).op (P.map (f i).op t) =
          P.map (pullback.fst N.map (f i)).op s := by
        rw [← ht]
        simp only [← Functor.map_comp_apply, ← op_comp, pullback.condition]
      _ = P.map (pullback.snd N.map (f i)).op (x i) :=
        restriction_eq_of_component_values P hprod hsingle f N.index x hx s hs'
          (pullback.fst N.map (f i)) i (pullback.snd N.map (f i)) pullback.condition
  · intro t' ht'
    apply Presieve.isSeparatedFor_singleton.mp
      (hsingle N.map N.mem_nisnevichPrecoverage).isSeparatedFor
    rw [ht]
    apply (hprod N.size _).injective
    funext j
    change P.map (N.inclusion j).op (P.map N.map.op t') = P.map (N.inclusion j).op s
    simpa only [← Functor.map_comp_apply, ← op_comp, N.inclusion_map, hs' j] using ht' (N.index j)

/-- A finite-product-preserving presheaf satisfying genuine singleton Nisnevich
descent is an ordinary Nisnevich sheaf. -/
theorem isSheaf_of_singleton_of_finiteCoproduct :
    Presieve.IsSheaf (nisnevichTopology S) P := by
  apply (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange P).mpr
  intro X R hR
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  exact isSheafFor_nisnevich_family_of_finiteCoproduct P hprod hsingle f hR

omit hsingle in
/-- For presheaves taking actual finite disjoint unions to products, ordinary
Nisnevich sheafness is exactly genuine singleton Nisnevich descent. The finite
product condition includes `Fin 0`, so empty covers are covered by this statement. -/
theorem isSheaf_iff_singleton_of_finiteCoproduct :
    Presieve.IsSheaf (nisnevichTopology S) P ↔
      ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
        Presieve.singleton q ∈ nisnevichPrecoverage S X →
          Presieve.IsSheafFor P (.singleton q) := by
  constructor
  · intro h X Y q hq
    exact (Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange P).mp h _ hq
  · intro hs
    exact isSheaf_of_singleton_of_finiteCoproduct P hprod hs

end AlgebraicGeometry.Scheme.SmoothSite
