/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.AffineLineEtaleCompactification

/-! # The actual overlap target retained inside the compactification

The target is the original pullback U ×[A1] Y, not U. Avoiding the whole infinity and
original finite boundary gives a unique map to this original overlap.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y Z : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
  (U : (Spec (.of (Polynomial k))).Opens)
  (z : Z ⟶ Spec (.of (Polynomial k)))
  (s : Z ⟶ Y) (H : IsPullback s (𝟙 _) p z)
  (hz : Set.range z = (U : Set (Spec (.of (Polynomial k))))ᶜ)

omit [Etale p] [QuasiCompact p] [IsSeparated p] in
include H hz in
/-- The full complement condition identifies the original pulled-back Z, including its support. -/
theorem range_originalBoundary : Set.range s = p ⁻¹' (U : Set (Spec (.of (Polynomial k))))ᶜ := by
  rw [← hz]
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (congrArg (fun a : Z ⟶ Spec (.of (Polynomial k)) => a w) H.w).symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback H y w hw.symm
    exact ⟨v, hv⟩

/-- The original overlap embeds openly into the constructed compactification. -/
def retainedInclusion : pullback U.ι p ⟶ compactification k p :=
  pullback.snd U.ι p ≫ inclusion k p

instance : IsOpenImmersion (retainedInclusion k p U) := by
  dsimp [retainedInclusion]
  infer_instance

include H hz in
/-- The retained target is exactly the complement of both full boundary components. -/
theorem range_retainedInclusion : Set.range (retainedInclusion k p U) =
    (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ inclusion k p))ᶜ := by
  have hB : Set.range (pullback.snd U.ι p) = (Set.range s)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι, range_originalBoundary k p U z s H hz]
    simp only [Set.preimage_compl, compl_compl]
  have hI : Set.range (infinityInclusion k p) = (Set.range (inclusion k p))ᶜ :=
    EtaleCompactification.range_infinityInclusion _ (projectiveMap k p)
  rw [hI]
  change Set.range (pullback.snd U.ι p ≫ inclusion k p) = _
  change Set.range ((inclusion k p) ∘ (pullback.snd U.ι p)) =
    ((Set.range (inclusion k p))ᶜ ∪ Set.range ((inclusion k p) ∘ s))ᶜ
  rw [Set.range_comp, Set.range_comp, hB]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ h
    rcases h with h | ⟨v, hv, he⟩
    · exact h ⟨y, rfl⟩
    · exact hy ((inclusion k p).isOpenEmbedding.injective he ▸ hv)
  · intro hx
    have hxI : x ∈ Set.range (inclusion k p) := by
      by_contra hn
      exact hx (Or.inl hn)
    obtain ⟨y, rfl⟩ := hxI
    refine ⟨y, ?_, rfl⟩
    intro hy
    exact hx (Or.inr ⟨y, hy, rfl⟩)

/-- A map avoiding both boundary components factors through the original overlap target. -/
def liftToRetained {T : Scheme.{u}} (g : T ⟶ compactification k p)
    (hg : Set.range g ⊆
      (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ inclusion k p))ᶜ) :
    T ⟶ pullback U.ι p :=
  IsOpenImmersion.lift (retainedInclusion k p U) g
    (by rw [range_retainedInclusion k p U z s H hz]; exact hg)

/-- The factorization retains the original compactification map literally. -/
@[reassoc (attr := simp)]
theorem liftToRetained_fac {T : Scheme.{u}} (g : T ⟶ compactification k p)
    (hg : Set.range g ⊆
      (Set.range (infinityInclusion k p) ∪ Set.range (s ≫ inclusion k p))ᶜ) :
    liftToRetained k p U z s H hz g hg ≫ retainedInclusion k p U = g :=
  IsOpenImmersion.lift_fac ..

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
