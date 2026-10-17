/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleNisnevich
public import Motivic.Topology.JacobsonOpenCover

/-! # Closed-point open neighborhoods give genuine small-Nisnevich covers -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace Motivic.FiniteEtaleSite
variable {S : Scheme.{u}} (W : FiniteEtaleSite S) [JacobsonSpace W.left]

/-- Closed points are used only to build a Zariski open cover. Residue-field splitting
at every point then follows from the actual open immersions, not a closed-point test
for arbitrary Nisnevich families. -/
theorem sieve_mem_of_closedPoint_open_neighborhoods (R : Sieve W)
    (h : ∀ x : W.left, IsClosed ({x} : Set W.left) →
      ∃ (V : FiniteEtaleSite S) (f : V ⟶ W),
        IsOpenImmersion f.left ∧ x ∈ Set.range f.left ∧ R f) :
    R ∈ nisnevichTopology S W := by
  classical
  choose V f hf hx hR using fun x : closedPoints W.left => h x.val x.property
  let : ∀ x, IsOpenImmersion (f x).left := hf
  let O := fun x : closedPoints W.left => (f x).left.opensRange
  have htop : (⨆ x, O x) = ⊤ := by
    apply TopologicalSpace.Opens.iSup_eq_top_of_closedPoint_neighborhoods
    intro x hc
    exact ⟨⟨x, hc⟩, hx ⟨x, hc⟩⟩
  have hpre : Presieve.ofArrows V f ∈ nisnevichPrecoverage S W := by
    apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    refine ⟨fun _ => inferInstance, ?_⟩
    intro w
    have hw : w ∈ (⨆ x, O x) := by rw [htop]; trivial
    obtain ⟨x, y, hy⟩ : ∃ x, ∃ y, (f x).left y = w := by
      simpa only [TopologicalSpace.Opens.mem_iSup, O, Scheme.Hom.mem_opensRange] using hw
    exact ⟨x, y, hy, inferInstance⟩
  apply (nisnevichTopology S).superset_covering
    ((Sieve.generate_le_iff _ _).mpr ?_) (Precoverage.generate_mem_toGrothendieck hpre)
  rintro _ _ ⟨x⟩
  exact hR x

end Motivic.FiniteEtaleSite
