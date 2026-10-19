/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.CommonRefinement
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Refinement

/-!
# Equal original Nisnevich germs agree at a common pointed neighborhood

Equality is measured in the already constructed point-fiber colimit. It gives
an actual refinement where representatives agree, hence equality of their
center germs on any common pointed neighborhood. Points need not be closed.
No new stalk notion or ordinary-cohomology acyclicity is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- Vanishing on an actual pointed étale restriction kills the original germ.
The residue-field isomorphism is that of the displayed map at its displayed point. -/
theorem germ_eq_zero_of_pointed_restriction {U : SmoothSite S} (g : U ⟶ X)
    [Etale g.left] (u : U.left) (hu : g.left u = x)
    [IsIso (g.left.residueFieldMap u)] (s : F.obj (op X))
    (hs : F.map g.op s = 0) : sectionToNisnevichPoint F X x s = 0 := by
  let R := NisnevichNeighborhood.ofResidueFieldIso g u hu
  apply (sectionToNisnevichPoint_eq_zero_iff F s).mpr
  refine ⟨R, ?_⟩
  let e : (nisnevichNeighborhoodFunctor X x).obj R ≅ U :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 _) ≫ U.hom = g.left ≫ X.hom
      simpa only [Category.id_comp] using (MorphismProperty.Over.w g).symm)
  have he : R.toBase = e.hom ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.id_comp _).symm
  rw [he, op_comp, F.map_comp, ConcreteCategory.comp_apply, hs, map_zero]

/-- A zero value of the original cocone is a zero germ at the neighborhood's own center. -/
theorem center_germ_eq_zero_of_nisnevichPointFiberCocone_eq_zero
    (N : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (hs : (nisnevichPointFiberCocone X x F).ι.app (op N) s = 0) :
    sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center s = 0 := by
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max (u + 1) v, u, max (u + 1) v} _
  have h : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op N) 0 := by
    simpa only [map_zero] using hs
  obtain ⟨M, q, hq⟩ := (isColimitNisnevichPointFiberCocone X x F).eq_iff' s 0 |>.mp h
  let g := (nisnevichNeighborhoodFunctor X x).map q.unop
  let R := NisnevichNeighborhood.ofResidueFieldIso g M.unop.center
    (NisnevichNeighborhood.map_center q.unop)
  apply (sectionToNisnevichPoint_eq_zero_iff F s).mpr
  refine ⟨R, ?_⟩
  let e : (nisnevichNeighborhoodFunctor
      ((nisnevichNeighborhoodFunctor X x).obj N) N.center).obj R ≅
        (nisnevichNeighborhoodFunctor X x).obj M.unop :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 _) ≫ ((nisnevichNeighborhoodFunctor X x).obj M.unop).hom =
        g.left ≫ ((nisnevichNeighborhoodFunctor X x).obj N).hom
      simpa only [Category.id_comp] using (MorphismProperty.Over.w g).symm)
  have he : R.toBase = e.hom ≫ g := by
    apply MorphismProperty.Over.Hom.ext
    exact (Category.id_comp _).symm
  have hq' : F.map g.op s = 0 := by
    change F.map g.op s = F.map g.op 0 at hq
    simpa only [map_zero] using hq
  rw [he, op_comp, F.map_comp, ConcreteCategory.comp_apply, hq', map_zero]

/-- The original point cocone identifies two representatives exactly when their
actual germs agree at that neighborhood's center. -/
theorem nisnevichPointFiberCocone_eq_iff_center_germ_eq
    (N : NisnevichNeighborhood X x)
    (s t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N))) :
    (nisnevichPointFiberCocone X x F).ι.app (op N) s =
        (nisnevichPointFiberCocone X x F).ι.app (op N) t ↔
      sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center s =
        sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj N) N.center t := by
  constructor
  · intro h
    have hz := center_germ_eq_zero_of_nisnevichPointFiberCocone_eq_zero F N (s - t)
      (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  · exact nisnevichPointFiberCocone_eq_of_center_germ_eq F N s t

/-- Equal original germs have equal pulled-back germs on every actual common
pointed refinement, including the canonical Čech neighborhood. -/
theorem common_refinement_center_germs_eq
    {N M P : NisnevichNeighborhood X x} (f : P ⟶ N) (g : P ⟶ M)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj M)))
    (hst : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op M) t) :
    sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj P) P.center
        (F.map ((nisnevichNeighborhoodFunctor X x).map f).op s) =
      sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj P) P.center
        (F.map ((nisnevichNeighborhoodFunctor X x).map g).op t) := by
  apply (nisnevichPointFiberCocone_eq_iff_center_germ_eq F P _ _).mp
  have hf := (nisnevichPointFiberCocone X x F).w f.op
  have hg := (nisnevichPointFiberCocone X x F).w g.op
  change F.map ((nisnevichNeighborhoodFunctor X x).map f).op ≫
    (nisnevichPointFiberCocone X x F).ι.app (op P) =
      (nisnevichPointFiberCocone X x F).ι.app (op N) at hf
  change F.map ((nisnevichNeighborhoodFunctor X x).map g).op ≫
    (nisnevichPointFiberCocone X x F).ι.app (op P) =
      (nisnevichPointFiberCocone X x F).ι.app (op M) at hg
  exact (ConcreteCategory.congr_hom hf s).trans
    (hst.trans (ConcreteCategory.congr_hom hg t).symm)

/-- On the literal common Čech neighborhood, equal original germs give equal
pulled-back center germs. The displayed iso has the identity underlying scheme map. -/
theorem common_cech_center_germs_eq
    (N M : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj M)))
    (hst : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op M) t) :
    sectionToNisnevichPoint F
        ((nisnevichNeighborhoodFunctor X x).obj (NisnevichNeighborhood.common N M))
        (NisnevichNeighborhood.commonPoint N M default)
        (F.map ((NisnevichNeighborhood.commonIso N M).hom ≫
          etalePullbackFst N.toBase M.toBase).op s) =
      sectionToNisnevichPoint F
        ((nisnevichNeighborhoodFunctor X x).obj (NisnevichNeighborhood.common N M))
        (NisnevichNeighborhood.commonPoint N M default)
        (F.map ((NisnevichNeighborhood.commonIso N M).hom ≫
          etalePullbackSnd N.toBase M.toBase).op t) := by
  simpa only [NisnevichNeighborhood.map_commonFst, NisnevichNeighborhood.map_commonSnd,
    NisnevichNeighborhood.common_center] using
    common_refinement_center_germs_eq F (NisnevichNeighborhood.commonFst N M)
      (NisnevichNeighborhood.commonSnd N M) s t hst

/-- Equal original point-fiber classes have equal germs on the literal smooth-site
Čech pullback at the canonical residue-field point, without a closed-point assumption. -/
theorem literal_cech_germs_eq
    (N M : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj M)))
    (hst : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op M) t) :
    sectionToNisnevichPoint F (etalePullback N.toBase M.toBase)
        (NisnevichNeighborhood.commonPoint N M default)
        (F.map (etalePullbackFst N.toBase M.toBase).op s) =
      sectionToNisnevichPoint F (etalePullback N.toBase M.toBase)
        (NisnevichNeighborhood.commonPoint N M default)
        (F.map (etalePullbackSnd N.toBase M.toBase).op t) := by
  let C := NisnevichNeighborhood.common N M
  let e := NisnevichNeighborhood.commonIso N M
  let d := F.map (etalePullbackFst N.toBase M.toBase).op s -
    F.map (etalePullbackSnd N.toBase M.toBase).op t
  have hd : sectionToNisnevichPoint F ((nisnevichNeighborhoodFunctor X x).obj C)
      C.center (F.map e.hom.op d) = 0 := by
    dsimp only [d]
    rw [map_sub, map_sub]
    apply sub_eq_zero.mpr
    simp only [← Functor.map_comp_apply, ← op_comp]
    exact common_cech_center_germs_eq F N M s t hst
  obtain ⟨R, hR⟩ := (sectionToNisnevichPoint_eq_zero_iff F _).mp hd
  let g := R.toBase ≫ e.hom
  have hg : g.left = R.toBase.left := by
    change R.toBase.left ≫ (𝟙 _) = R.toBase.left
    exact Category.comp_id _
  let : Etale g.left := by rw [hg]; infer_instance
  let : IsIso (g.left.residueFieldMap R.center) := by rw [hg]; infer_instance
  have hc : g.left R.center = NisnevichNeighborhood.commonPoint N M default := by
    rw [hg]
    exact R.toBase_center
  have hz : F.map g.op d = 0 := by
    dsimp only [g]
    rw [op_comp, F.map_comp, ConcreteCategory.comp_apply]
    exact hR
  have h := germ_eq_zero_of_pointed_restriction F g R.center hc d hz
  exact sub_eq_zero.mp (by simpa only [d, map_sub] using h)

end AlgebraicGeometry.Scheme.SmoothSite
