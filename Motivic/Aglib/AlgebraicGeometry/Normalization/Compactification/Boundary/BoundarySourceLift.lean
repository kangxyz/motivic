module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.DisjointBoundary
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ChartBoundary
/-! # Finite source boundary over one fixed target presentation

The original étale source is retained in its actual finite normalization. On any
open where the original map is finite there are no new missing points. Thus a
finite target bad boundary controls the whole source boundary, without choosing
another projection and without assuming source-boundary finiteness.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]

/-- The original open source contains every point over an integral chart. -/
theorem mem_range_inclusion_of_integral_chart (U : X.Opens)
    [IsIntegralHom (pullback.snd f U.ι)]
    (x : (genericMap X f).normalization)
    (hx : (genericMap X f).fromNormalization x ∈ U) :
    x ∈ Set.range (inclusion X f) := by
  let e := normalizationIso X f
  have ho : e.inv ≫ f.fromNormalization = (genericMap X f).fromNormalization := by
    rw [← normalizationIso_hom_over X f]
    simp only [e, Iso.inv_hom_id_assoc]
  have hx' : f.fromNormalization (e.inv x) ∈ U := by
    simpa only [← Scheme.Hom.comp_apply, ho] using hx
  obtain ⟨y, hy⟩ := f.mem_range_toNormalization_of_integral_chart U (e.inv x) hx'
  refine ⟨y, ?_⟩
  have he : f.toNormalization ≫ e.hom = inclusion X f := by simp [e, normalizationIso]
  have hpoint := congrArg (fun z => e.hom z) hy
  simp only [← Scheme.Hom.comp_apply, he, Iso.inv_hom_id] at hpoint
  exact hpoint

/-- Full source infinity lies over the actual complement of the finite target chart. -/
theorem infinity_image_outside_integral_chart (U : X.Opens)
    [IsIntegralHom (pullback.snd f U.ι)] (x : infinity X f) :
    (infinityInclusion X f ≫ (genericMap X f).fromNormalization) x ∉ U := by
  intro hx
  have hi := mem_range_inclusion_of_integral_chart X f U (infinityInclusion X f x) hx
  have hn : infinityInclusion X f x ∈ (Set.range (inclusion X f))ᶜ := by
    rw [← range_infinityInclusion]
    exact ⟨x, rfl⟩
  exact hn hi

/-- One fixed finite target bad boundary forces the entire original source infinity
finite over the same base. The bad boundary may be nonreduced or disconnected. -/
theorem finite_infinity_of_finite_target_boundary
    {S D : Scheme.{u}} (q : X ⟶ S) [IsProper q]
    (d : D ⟶ X) [IsFinite (d ≫ q)] (U : X.Opens)
    [IsIntegralHom (pullback.snd f U.ι)]
    (hbad : (U : Set X)ᶜ ⊆ Set.range d) :
    IsFinite (infinityInclusion X f ≫ (genericMap X f).fromNormalization ≫ q) := by
  let g := infinityInclusion X f ≫ (genericMap X f).fromNormalization
  have : IsFinite g := by dsimp [g]; infer_instance
  let p := g ≫ q
  have : IsProper p := by dsimp [p, g]; infer_instance
  have hp : ∀ s : S, (p ⁻¹' {s}).Finite := by
    intro s
    have hD : (d '' ((d ≫ q) ⁻¹' {s})).Finite :=
      ((d ≫ q).finite_preimage_singleton s).image d
    apply (g.finite_preimage hD).subset
    intro x hx
    obtain ⟨z, hz⟩ := hbad (infinity_image_outside_integral_chart X f U x)
    refine ⟨z, ?_, hz⟩
    change (d ≫ q) z = s
    change q (g x) = s at hx
    simpa only [Scheme.Hom.comp_apply, hz, g] using hx
  have : LocallyQuasiFinite p := LocallyQuasiFinite.of_finite_preimage_singleton p hp
  exact IsFinite.of_isProper_of_locallyQuasiFinite p
end AlgebraicGeometry.Scheme.EtaleCompactification
