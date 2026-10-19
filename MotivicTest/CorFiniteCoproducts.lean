/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Finite

/-! # Consumers of gluing on the actual finite total scheme -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorFiniteCoproducts

variable (k : Type u) [Field k]

example {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    IsColimit (Cofan.mk (Cor.mk (SmoothSite.finiteCoproduct Y))
      (fun i => (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i))) :=
  Cor.finiteCoproductIsColimit k Y

example {n : ℕ} {T : Cor k} {Y : Fin n → SmoothSite (Spec (.of k))}
    (f : ∀ i, Cor.mk (Y i) ⟶ T) (i : Fin n) :
    (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫
      Cor.finiteCoproductDesc k f = f i := Cor.finiteCoproductι_desc k f i

example {T : Cor k} (Y : Fin 0 → SmoothSite (Spec (.of k)))
    (α β : Cor.mk (SmoothSite.finiteCoproduct Y) ⟶ T) : α = β :=
  Cor.finiteCoproduct_hom_ext k (fun i => Fin.elim0 i)

example {n : ℕ} {T T' : Cor k} {Y : Fin n → SmoothSite (Spec (.of k))}
    (f : ∀ i, Cor.mk (Y i) ⟶ T) (g : T ⟶ T')
    (h : Cor.mk (SmoothSite.finiteCoproduct Y) ⟶ T')
    (w : ∀ i, f i ≫ g = (Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i) ≫ h) :
    Cor.finiteCoproductDesc k f ≫ g = h := Cor.finiteCoproductDesc_comp_eq k f g h w

example {n : ℕ} {X : SmoothSite (Spec (.of k))}
    {Y : Fin n → SmoothSite (Spec (.of k))} (f : ∀ i, Y i ⟶ X) :
    Cor.finiteCoproductDesc k (fun i => (Cor.graphFunctor k).map (f i)) =
      (Cor.graphFunctor k).map (SmoothSite.finiteCoproductDesc f) :=
  Cor.finiteCoproductDesc_graph k f

end MotivicTest.CorFiniteCoproducts
