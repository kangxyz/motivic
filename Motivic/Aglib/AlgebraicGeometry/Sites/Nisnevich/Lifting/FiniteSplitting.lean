/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.QuasiFinite

/-!
# Finite support splitting over pointed Nisnevich neighborhoods

The algebraic splitting is supplied by Andrew Yang's
`Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq`
in mathlib. We interpret its idempotents as actual clopen subschemes and remove
its empty-fiber remainder by the closed-image property of a finite morphism.
No reducedness or flatness assumption is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A complete family of orthogonal idempotents covers the entire spectrum by
pairwise disjoint clopen principal opens, including in the zero ring. -/
lemma completeOrthogonalIdempotents_basicOpen_partition
    {A : Type u} [CommRing A] {I : Type*} [Fintype I]
    {e : I → A} (he : CompleteOrthogonalIdempotents e) :
    (∀ i, IsClopen (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum A))) ∧
    Pairwise (fun i j ↦ Disjoint (PrimeSpectrum.basicOpen (e i))
      (PrimeSpectrum.basicOpen (e j))) ∧
    (⨆ i, PrimeSpectrum.basicOpen (e i)) = ⊤ := by
  classical
  refine ⟨fun i ↦ PrimeSpectrum.isClopen_iff.mpr ⟨e i, he.idem i, rfl⟩, ?_, ?_⟩
  · intro i j hij
    rw [disjoint_iff, ← PrimeSpectrum.basicOpen_mul, he.ortho hij,
      PrimeSpectrum.basicOpen_zero]
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← he.complete]
    exact Ideal.sum_mem _ (fun i _ ↦ Ideal.subset_span (Set.mem_range_self i))

/-- A finite morphism can be shrunk away from a closed part missing a chosen
fiber. The result controls the entire inverse image of the new base open. -/
lemma exists_open_preimage_disjoint_of_isFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (C : Set X) (hC : IsClosed C) (y : Y)
    (hy : ∀ x ∈ C, f x ≠ y) :
    ∃ U : Y.Opens, y ∈ U ∧ Disjoint (f ⁻¹' (U : Set Y)) C := by
  let U : Y.Opens := ⟨(f '' C)ᶜ, (f.isClosedMap C hC).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hy x hx hxy
  · exact Set.disjoint_left.mpr (fun x hx hxc ↦ hx ⟨x, hxc, rfl⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-- An affine finite morphism admits a pointed Nisnevich base neighborhood on
which its entire pullback is partitioned into finitely many clopen finite
pieces, each with a singleton fiber over the distinguished point. The square
is an actual pullback square of schemes, and the residue-field isomorphism is
induced by the neighborhood morphism. An empty fiber gives an empty partition.
-/
theorem exists_nisnevich_finiteSplitting_spec
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (s : PrimeSpectrum R) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of R)), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (T : Scheme.{u}) (a : T ⟶ Spec (.of A)) (b : T ⟶ U),
      IsPullback a b (Spec.map (CommRingCat.ofHom (algebraMap R A))) g ∧
    ∃ (n : ℕ) (V : Fin n → T.Opens),
      (∀ i, IsClopen (V i : Set T) ∧ IsFinite ((V i).ι ≫ b)) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ (⨆ i, V i) = ⊤ ∧
      ∀ i, ∃ v : V i, b v.1 = u ∧ ∀ v' : V i, b v'.1 = u → v' = v := by
  classical
  obtain ⟨R', _, _, _, P, _, _, n, e, he, P', _, _, hres, hmem, huniq⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (S := A) s.asIdeal
  let φ : CommRingCat.of R ⟶ .of R' := CommRingCat.ofHom (algebraMap R R')
  let ψ : CommRingCat.of R' ⟶ .of (R' ⊗[R] A) :=
    CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A))
  let b₀ := Spec.map ψ
  let a₀ : Spec (.of (R' ⊗[R] A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom)
  let D : Fin (n + 1) → (Spec (.of (R' ⊗[R] A))).Opens :=
    fun i ↦ PrimeSpectrum.basicOpen (e i)
  have hD := completeOrthogonalIdempotents_basicOpen_partition he
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have : IsFinite b₀ := (IsFinite.SpecMap_iff ψ).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have hb₀ (z : PrimeSpectrum (R' ⊗[R] A)) (hz : b₀ z = ⟨P, ‹_›⟩) :
      z.asIdeal.LiesOver P := ⟨congr(($hz).asIdeal).symm⟩
  obtain ⟨W, hPW, hWD⟩ := exists_open_preimage_disjoint_of_isFinite b₀
    (D (.last n)) (hD.1 (.last n)).1 ⟨P, ‹_›⟩ (by
      intro z hz hmap
      exact hz (huniq z.asIdeal z.isPrime (hb₀ z hmap)).1)
  let b := b₀ ∣_ W
  let V : Fin n → (b₀ ⁻¹ᵁ W).toScheme.Opens :=
    fun i ↦ (b₀ ⁻¹ᵁ W).ι ⁻¹ᵁ D i.castSucc
  have hVclosed (i : Fin n) : IsClopen (V i : Set (b₀ ⁻¹ᵁ W)) :=
    (hD.1 i.castSucc).preimage (b₀ ⁻¹ᵁ W).ι.continuous
  have hVfinite (i : Fin n) : IsFinite ((V i).ι ≫ b) := by
    have : IsClosedImmersion (V i).ι := .of_isPreimmersion _ (by
      simpa only [Scheme.Opens.range_ι] using (hVclosed i).1)
    infer_instance
  have hsq : IsPullback a₀ b₀ (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map φ) := by
    exact (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct R R' A)).flip
  have hres' : IsIso ((Spec.map φ).residueFieldMap ⟨P, ‹_›⟩) :=
    Scheme.Spec.isIso_residueFieldMap_of_bijective φ ⟨P, ‹_›⟩ s.asIdeal
      (P.over_def _) hres
  refine ⟨W, W.ι ≫ Spec.map φ, inferInstance, ⟨⟨P, ‹_›⟩, hPW⟩, ?_, ?_,
    (b₀ ⁻¹ᵁ W), (b₀ ⁻¹ᵁ W).ι ≫ a₀, b,
    ((isPullback_morphismRestrict b₀ W).paste_vert hsq.flip).flip,
    n, V, fun i ↦ ⟨hVclosed i, hVfinite i⟩, ?_, ?_, ?_⟩
  · exact PrimeSpectrum.ext (P.over_def _).symm
  · rw [Scheme.residueFieldMap_comp]
    simp only [Scheme.Opens.ι_apply]
    infer_instance
  · intro i j hij
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro z hz
    have hz' : z.1 ∈ D i.castSucc ⊓ D j.castSucc := hz
    rw [disjoint_iff.mp (hD.2.1 (fun h ↦ hij (Fin.castSucc_injective n h)))] at hz'
    exact hz'
  · apply le_antisymm le_top
    intro z _
    have hz : z.1 ∈ ⨆ i, D i := by rw [hD.2.2]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    apply TopologicalSpace.Opens.mem_iSup.mpr
    revert hj
    refine Fin.lastCases ?_ (fun i hi ↦ ⟨i, hi⟩) j
    intro hzD
    exact (Set.disjoint_left.mp hWD z.2 hzD).elim
  · intro i
    have hPi : b₀ (⟨P' i, inferInstance⟩ : PrimeSpectrum (R' ⊗[R] A)) = ⟨P, ‹_›⟩ :=
      PrimeSpectrum.ext ((P' i).over_def P).symm
    let z : (b₀ ⁻¹ᵁ W).toScheme := ⟨⟨P' i, inferInstance⟩, by
      change b₀ _ ∈ W
      rw [hPi]
      exact hPW⟩
    refine ⟨⟨z, hmem i⟩, ?_, ?_⟩
    · apply Subtype.ext
      exact (morphismRestrict_base_coe b₀ W z).trans hPi
    · intro v hv
      apply Subtype.ext
      apply Subtype.ext
      apply PrimeSpectrum.ext
      exact (huniq v.1.1.asIdeal v.1.1.isPrime
        (hb₀ v.1.1 ((morphismRestrict_base_coe b₀ W v.1).symm.trans
          (congrArg Subtype.val hv)))).2 i v.2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The finite splitting theorem over an arbitrary base scheme, expressed by
an actual pullback square. Affineness is used only on an open neighborhood of
the chosen base point. -/
theorem exists_nisnevich_finiteSplitting_square
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (T : Scheme.{u}) (a : T ⟶ X) (b : T ⟶ U), IsPullback a b f g ∧
    ∃ (n : ℕ) (V : Fin n → T.Opens),
      (∀ i, IsClopen (V i : Set T) ∧ IsFinite ((V i).ι ≫ b)) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ (⨆ i, V i) = ⊤ ∧
      ∀ i, ∃ v : V i, b v.1 = u ∧ ∀ v' : V i, b v'.1 = u → v' = v := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hsW, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ s) isOpen_univ
  have hV := hW.preimage f
  have : (f.app W).hom.Finite := f.finite_app W hW
  algebraize [(f.app W).hom]
  obtain ⟨U, g, hg, u, hu, hres, T, a, b, hsq, n, V, hVfin, hVdisj, hVtop, hVfib⟩ :=
    exists_nisnevich_finiteSplitting_spec (R := Γ(S, W)) (A := Γ(X, f ⁻¹ᵁ W))
      (hW.primeIdealOf ⟨s, hsW⟩)
  have hsq₀ : IsPullback hV.fromSpec (Spec.map (f.app W)) f hW.fromSpec := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback
    · simpa only [Scheme.Hom.app_eq_appLE] using
        (IsAffineOpen.SpecMap_appLE_fromSpec f hW hV le_rfl).symm
    · rw [hW.opensRange_fromSpec, hV.opensRange_fromSpec]
  refine ⟨U, g ≫ hW.fromSpec, inferInstance, u, ?_, ?_, T, a ≫ hV.fromSpec, b,
    hsq.paste_horiz hsq₀, n, V, hVfin, hVdisj, hVtop, hVfib⟩
  · rw [Scheme.Hom.comp_apply, hu]
    exact hW.fromSpec_primeIdealOf ⟨s, hsW⟩
  · rw [Scheme.residueFieldMap_comp]
    infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A finite morphism splits Nisnevich-locally into a complete finite clopen
partition whose pieces have exactly one point over the distinguished base
point. The decomposition is on the canonical scheme-theoretic pullback,
retains all nilpotents, and also applies when the original fiber is empty. -/
theorem exists_nisnevich_finiteSplitting
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (V : Fin n → (pullback f g).Opens),
      (∀ i, IsClopen (V i : Set (pullback f g : Scheme)) ∧
        IsFinite ((V i).ι ≫ pullback.snd f g)) ∧
      Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧ (⨆ i, V i) = ⊤ ∧
      ∀ i, ∃ v : V i, pullback.snd f g v.1 = u ∧
        ∀ v' : V i, pullback.snd f g v'.1 = u → v' = v := by
  obtain ⟨U, g, hg, u, hu, hres, T, a, b, hsq, n, V, hVfin, hVdisj, hVtop, hVfib⟩ :=
    exists_nisnevich_finiteSplitting_square f s
  let e := hsq.isoPullback
  let W : Fin n → (pullback f g).Opens := fun i ↦ e.inv ⁻¹ᵁ V i
  have he (t : T) : e.inv (e.hom t) = t := by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
    rfl
  have hW (i : Fin n) : IsClopen (W i : Set (pullback f g : Scheme)) :=
    (hVfin i).1.preimage e.inv.continuous
  refine ⟨U, g, hg, u, hu, hres, n, W, ?_, ?_, e.inv.iSup_preimage_eq_top hVtop, ?_⟩
  · intro i
    have : IsClosedImmersion (W i).ι := .of_isPreimmersion _ (by
      simpa only [Scheme.Opens.range_ι] using (hW i).1)
    exact ⟨hW i, inferInstance⟩
  · intro i j hij
    change Disjoint (e.inv ⁻¹ᵁ V i) (e.inv ⁻¹ᵁ V j)
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf,
      disjoint_iff.mp (hVdisj hij), Scheme.Hom.preimage_bot]
  · intro i
    obtain ⟨v, hv, huniq⟩ := hVfib i
    have hvW : e.hom v.1 ∈ W i := by
      change e.inv (e.hom v.1) ∈ V i
      simpa only [he] using v.2
    refine ⟨⟨e.hom v.1, hvW⟩, ?_, ?_⟩
    · simpa only [← Scheme.Hom.comp_apply, e, hsq.isoPullback_hom_snd] using hv
    · intro w hw
      apply Subtype.ext
      apply e.inv.homeomorph.injective
      change e.inv w.1 = e.inv (e.hom v.1)
      rw [he]
      apply congrArg Subtype.val (huniq ⟨e.inv w.1, w.2⟩ ?_)
      simpa only [← Scheme.Hom.comp_apply, e, hsq.isoPullback_inv_snd] using hw

end AlgebraicGeometry
