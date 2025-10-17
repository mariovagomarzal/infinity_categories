/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Pfun
import InfinityCategories.Data.NatIndex

set_option linter.style.longLine false

/-!
# Single-sorted categories

In this file we define the notion of single-sorted $n$-category and
single-sorted $\omega$-category.

## Notation

- `g ♯[i] f ← composable_gf` denotes the composition of `g` and `f` at the
  `i`-th level, where `composable_gf` is a proof that the source of `g` is the
  target of `f` at that level.
-/

-- TODO: Document the file.

universe u

namespace SingleSortedCategories

class SingleSortedStruct (Obj : Type u)
    (index : Type) [NatIndex index] where
  sc : index → Obj → Obj
  tg : index → Obj → Obj
  pcomp : index → Obj → Obj →. Obj
  pcomp_dom : ∀ {i : index} {f g : Obj},
    (pcomp i g f).Dom ↔ sc i g = tg i f

scoped notation:100 g " sc_is_tg[" i:100 "] " f:100 =>
  SingleSortedStruct.sc i g = SingleSortedStruct.tg i f

scoped notation:100 g " ♯[" i:100 "] " f:100 =>
  SingleSortedStruct.pcomp i g f

scoped notation:80 pcomp " ← " prf:80 =>
  Part.get pcomp (SingleSortedStruct.pcomp_dom.mpr prf)

class SingleSortedCategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedStruct Obj index where
  scsc : ∀ {i : index} {f : Obj},
    sc i (sc i f) = sc i f
  tgsc : ∀ {i : index} {f : Obj},
    tg i (sc i f) = sc i f
  sctg : ∀ {i : index} {f : Obj},
    sc i (tg i f) = tg i f
  tgtg : ∀ {i : index} {f : Obj},
    tg i (tg i f) = tg i f
  sc_comp_is_sc : ∀ {i : index} {f g : Obj}
      (composable_gf : g sc_is_tg[i] f),
    sc i (g ♯[i] f ← composable_gf) = sc i f
  tg_comp_is_tg : ∀ {i : index} {f g : Obj}
      (composable_gf : g sc_is_tg[i] f),
    tg i (g ♯[i] f ← composable_gf) = tg i g
  comp_sc_is_id : ∀ {i : index} {f : Obj},
    f ♯[i] (sc i f) ← tgsc.symm = f
  comp_tg_is_id : ∀ {i : index} {f : Obj},
    (tg i f) ♯[i] f ← sctg = f
  assoc : ∀ {i : index} {f g h : Obj}
      (composable_gf : g sc_is_tg[i] f)
      (composable_hg : h sc_is_tg[i] g),
    let composable_h_gf : h sc_is_tg[i] (g ♯[i] f ← composable_gf) :=
      composable_hg.trans (tg_comp_is_tg composable_gf).symm
    let composable_hg_f : (h ♯[i] g ← composable_hg) sc_is_tg[i] f :=
      (sc_comp_is_sc composable_hg).trans composable_gf
    (h ♯[i] (g ♯[i] f ← composable_gf) ← composable_h_gf) =
      ((h ♯[i] g ← composable_hg) ♯[i] f ← composable_hg_f)

class SingleSorted2CategoryFamily (Obj : Type u)
    (index : Type) [NatIndex index]
    extends SingleSortedCategoryFamily Obj index where
  sckscj : ∀ {k : index} {j : Fin k} {f : Obj},
    sc k (sc j f) = sc j f
  scjsck : ∀ {k : index} {j : Fin k} {f : Obj},
    sc j (sc k f) = sc j f
  scjtgk : ∀ {k : index} {j : Fin k} {f : Obj},
    sc j (tg k f) = sc j f
  tgktgj : ∀ {k : index} {j : Fin k} {f : Obj},
    tg k (tg j f) = tg j f
  tgjtgk : ∀ {k : index} {j : Fin k} {f : Obj},
    tg j (tg k f) = tg j f
  tgjsck : ∀ {k : index} {j : Fin k} {f : Obj},
    tg j (sc k f) = tg j f
  -- Method for j-sources
  composable_j_sc {k : index} {j : Fin k} {f g : Obj} (composable_j_gf : g sc_is_tg[(j : index)] f) : (sc k g) sc_is_tg[(j : index)] (sc k f) := by
    calc
      sc j (sc k g) = sc j g        := scjsck
      _             = tg j f        := composable_j_gf
      _             = tg j (sc k f) := tgjsck.symm
  -- Method for j-targets
  composable_j_tg {k : index} {j : Fin k} {f g : Obj} (composable_j_gf : g sc_is_tg[(j : index)] f) : (tg k g) sc_is_tg[(j : index)] (tg k f) := by
    calc
      sc j (tg k g) = sc j g        := scjtgk
      _             = tg j f        := composable_j_gf
      _             = tg j (tg k f) := tgjtgk.symm
  sc_comp_is_comp_sc : ∀ {k : index} {j : Fin k} {f g : Obj}
      (composable_j_gf : g sc_is_tg[(j : index)] f),
    sc k (g ♯[(j : index)] f ← composable_j_gf)
    = ((sc k g) ♯[(j : index)] (sc k f)) ← composable_j_sc composable_j_gf
  tg_comp_is_comp_tg : ∀ {k : index} {j : Fin k} {f g : Obj}
      (composable_j_gf : g sc_is_tg[(j : index)] f),
    tg k (g ♯[(j : index)] f ← composable_j_gf)
    = ((tg k g) ♯[(j : index)] (tg k f)) ← composable_j_tg composable_j_gf
  -- Method for left exchange
  composable_k_left {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (composable_k_g2g1 : g₂ sc_is_tg[(k : index)] g₁)
      (composable_k_f2f1 : f₂ sc_is_tg[(k : index)] f₁)
      (composable_j_g2f2 : g₂ sc_is_tg[(j : index)] f₂)
      (composable_j_g1f1 : g₁ sc_is_tg[(j : index)] f₁) :
    (g₂ ♯[(j : index)] f₂ ← composable_j_g2f2) sc_is_tg[(k : index)] (g₁ ♯[(j : index)] f₁ ← composable_j_g1f1) := by
      calc
        sc k (g₂ ♯[(j : index)] f₂ ← composable_j_g2f2) = (sc k g₂) ♯[(j : index)] (sc k f₂) ← _           := sc_comp_is_comp_sc composable_j_g2f2
        _                                               = (tg k g₁) ♯[(j : index)] (sc k f₂) ← _           := congrArg (fun x => (x ♯[(j : index)] (sc k f₂)) ← _) composable_k_g2g1
        _                                               = (tg k g₁) ♯[(j : index)] (tg k f₁) ← _           := congrArg (fun x => ((tg k g₁) ♯[(j : index)] x) ← _) composable_k_f2f1
        _                                               = tg k (g₁ ♯[(j : index)] f₁ ← composable_j_g1f1)  := (tg_comp_is_comp_tg composable_j_g1f1).symm
  -- Method for right exchange
  composable_k_right {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (composable_k_g2g1 : g₂ sc_is_tg[(k : index)] g₁)
      (composable_k_f2f1 : f₂ sc_is_tg[(k : index)] f₁)
      (composable_j_g2f2 : g₂ sc_is_tg[(j : index)] f₂)
      (composable_j_g1f1 : g₁ sc_is_tg[(j : index)] f₁) :
    (g₂ ♯[(k : index)] g₁ ← composable_k_g2g1) sc_is_tg[(j : index)] (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1) := by
      calc
        sc j (g₂ ♯[(k : index)] g₁ ← composable_k_g2g1) = sc j (sc k (g₂ ♯[(k : index)] g₁ ← composable_k_g2g1))  := sckscj.symm
        _                                               = sc j (sc k g₁)                                          := congrArg (fun x => sc j x) sc_comp_is_sc
        _                                               = sc j g₁                                                 := scjsck
        _                                               = tg j f₁                                                 := composable_j_g1f1
        _                                               = tg j (sc k f₁)                                          := tgjsck.symm 
        _                                               = tg j (sc k (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1))  := congrArg (fun x => tg j x) sc_comp_is_sc.symm
        _                                               = tg j (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1)         := tgsck
  exchange : ∀ {k : index} {j : Fin k} {f₁ f₂ g₁ g₂ : Obj}
      (composable_k_g2g1 : g₂ sc_is_tg[(k : index)] g₁)
      (composable_k_f2f1 : f₂ sc_is_tg[(k : index)] f₁)
      (composable_j_g2f2 : g₂ sc_is_tg[(j : index)] f₂)
      (composable_j_g1f1 : g₁ sc_is_tg[(j : index)] f₁),
    ((g₂ ♯[(j : index)] f₂ ← composable_j_g2f2) ♯[(k : index)] (g₁ ♯[(j : index)] f₁ ← composable_j_g1f1)) ← composable_k_left composable_k_g2g1 composable_k_f2f1 composable_j_g2f2 composable_j_g1f1
    = ((g₂ ♯[(k : index)] g₁ ← composable_k_g2g1) ♯[(j : index)]  (f₂ ♯[(k : index)] f₁ ← composable_k_f2f1)) ← composable_k_right composable_k_g2g1 composable_k_f2f1 composable_j_g2f2 composable_j_g1f1


  -- TODO: Implement the remaining axiom of single-sorted 2-categories.

@[ext]
class SingleSortedCategory (Obj : Type u)
    extends SingleSortedCategoryFamily Obj (Fin 1)

@[ext]
class SingleSorted2Category (Obj : Type*)
    extends SingleSorted2CategoryFamily Obj (Fin 2)

@[ext]
class SingleSortedNCategory (Obj : Type*) (index : Nat)
    extends SingleSorted2CategoryFamily Obj (Fin index)

@[ext]
class SingleSortedOmegaCategory (Obj : Type*)
    extends SingleSortedStruct Obj Nat

end SingleSortedCategories
