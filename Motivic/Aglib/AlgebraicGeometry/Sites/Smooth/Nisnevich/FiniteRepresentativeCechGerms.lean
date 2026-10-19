/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.RepresentativeCechGerms
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.FiniteCoproductCechPoints

/-! # Actual designated Čech matching for a finite family of germ representatives -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
  {n : ℕ} (y : Fin n → Y.left) (N : ∀ i, NisnevichNeighborhood Y (y i))

set_option quotPrecheck false in
local notation "V" => (fun i => (nisnevichNeighborhoodFunctor Y (y i)).obj (N i))
set_option quotPrecheck false in
local notation "q" => (fun i => (N i).toBase)
set_option quotPrecheck false in
local notation "Q" => (finiteCoproductDesc q)

/-- The actual total Čech matching condition follows from representing a single
original germ tuple. No compatibility condition on Čech germs is an input. -/
theorem finite_representative_cech_germs_eq
    (a : ∀ z : Y.left, (nisnevichPointFiberCocone Y z F).pt)
    (s : ∀ i, F.obj (op (V i)))
    (hs : ∀ i, (nisnevichPointFiberCocone Y (y i) F).ι.app (op (N i)) (s i) = a (y i))
    (t : F.obj (op (finiteCoproduct V)))
    (ht : ∀ i, F.map (finiteCoproductι V i).op t = s i)
    (w : (etalePullback Q Q).left)
    (hfst : ∃ i, (etalePullbackFst Q Q).left w =
      (finiteCoproductι V i).left (N i).center)
    (hsnd : ∃ j, (etalePullbackSnd Q Q).left w =
      (finiteCoproductι V j).left (N j).center) :
    sectionToNisnevichPoint F (etalePullback Q Q) w
        (F.map (etalePullbackFst Q Q).op t) =
      sectionToNisnevichPoint F (etalePullback Q Q) w
        (F.map (etalePullbackSnd Q Q).op t) := by
  obtain ⟨i, hi⟩ := hfst
  obtain ⟨j, hj⟩ := hsnd
  obtain ⟨w', hw', hwi, hwj, hres⟩ :=
    exists_finiteCoproductCechPoint q i j (N i).center (N j).center w hi hj
  subst w
  let := hres
  have hpair := representative_pair_cech_germs_eq F a (N i) (N j)
    (s i) (s j) (hs i) (hs j) w' hwi hwj
  have hrestricted :
      sectionToNisnevichPoint F (etalePullback (q i) (q j)) w'
          (F.map (finiteCoproductCechMap q i j).op
            (F.map (etalePullbackFst Q Q).op t)) =
        sectionToNisnevichPoint F (etalePullback (q i) (q j)) w'
          (F.map (finiteCoproductCechMap q i j).op
            (F.map (etalePullbackSnd Q Q).op t)) := by
    simp only [← Functor.map_comp_apply, ← op_comp]
    rw [finiteCoproductCechMap_fst, finiteCoproductCechMap_snd]
    simp only [op_comp, F.map_comp, ConcreteCategory.comp_apply, ht]
    exact hpair
  have h := germs_eq_of_restricted_germs_eq F (finiteCoproductCechMap q i j) w'
    (F.map (etalePullbackFst Q Q).op t) (F.map (etalePullbackSnd Q Q).op t) hrestricted
  exact h

/-- This is the literal designated-set condition required by controlled Čech
kernel evaluation, with membership in the actual range of the center injections. -/
theorem finite_representative_cech_matching
    (a : ∀ z : Y.left, (nisnevichPointFiberCocone Y z F).pt)
    (t : F.obj (op (finiteCoproduct V)))
    (ht : ∀ i, (nisnevichPointFiberCocone Y (y i) F).ι.app (op (N i))
      (F.map (finiteCoproductι V i).op t) = a (y i)) :
    ∀ w : (etalePullback Q Q).left,
      (etalePullbackFst Q Q).left w ∈
        Set.range (fun i => (finiteCoproductι V i).left (N i).center) →
      (etalePullbackSnd Q Q).left w ∈
        Set.range (fun i => (finiteCoproductι V i).left (N i).center) →
      sectionToNisnevichPoint F (etalePullback Q Q) w
          (F.map (etalePullbackFst Q Q).op t) =
        sectionToNisnevichPoint F (etalePullback Q Q) w
          (F.map (etalePullbackSnd Q Q).op t) := by
  rintro w ⟨i, hi⟩ ⟨j, hj⟩
  exact finite_representative_cech_germs_eq F y N a
    (fun i => F.map (finiteCoproductι V i).op t) ht t (fun _ => rfl) w
    ⟨i, hi.symm⟩ ⟨j, hj.symm⟩

/-- Original Nisnevich sheaf gluing supplies an actual total section whose
Čech germs match at all designated points. This is genuine matching, not an input law. -/
theorem exists_section_with_finite_representative_cech_matching
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (a : ∀ z : Y.left, (nisnevichPointFiberCocone Y z G.obj).pt)
    (s : ∀ i, G.obj.obj (op (V i)))
    (hs : ∀ i, (nisnevichPointFiberCocone Y (y i) G.obj).ι.app (op (N i))
      (s i) = a (y i)) :
    ∃ t : G.obj.obj (op (finiteCoproduct V)),
      (∀ i, G.obj.map (finiteCoproductι V i).op t = s i) ∧
      ∀ w : (etalePullback Q Q).left,
        (etalePullbackFst Q Q).left w ∈
          Set.range (fun i => (finiteCoproductι V i).left (N i).center) →
        (etalePullbackSnd Q Q).left w ∈
          Set.range (fun i => (finiteCoproductι V i).left (N i).center) →
        sectionToNisnevichPoint.{u, 0} G.obj (etalePullback Q Q) w
            (G.obj.map (etalePullbackFst Q Q).op t) =
          sectionToNisnevichPoint.{u, 0} G.obj (etalePullback Q Q) w
            (G.obj.map (etalePullbackSnd Q Q).op t) := by
  obtain ⟨t, ht⟩ := exists_section_finiteCoproduct G V s
  refine ⟨t, ht, finite_representative_cech_matching.{u, 0} G.obj y N a t ?_⟩
  intro i
  rw [ht i]
  exact hs i

end AlgebraicGeometry.Scheme.SmoothSite
