/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import Mathlib.Data.Pfun
import InfinityCategories.Data.NatIndex

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
  idemp_sc_sc : ∀ {i : index} {f : Obj},
    sc i (sc i f) = sc i f
  idemp_tg_sc : ∀ {i : index} {f : Obj},
    tg i (sc i f) = sc i f
  idemp_sc_tg : ∀ {i : index} {f : Obj},
    sc i (tg i f) = tg i f
  idemp_tg_tg : ∀ {i : index} {f : Obj},
    tg i (tg i f) = tg i f
  sc_comp_is_sc : ∀ {i : index} {f g : Obj}
      (composable_gf : g sc_is_tg[i] f),
    sc i (g ♯[i] f ← composable_gf) = sc i f
  tg_comp_is_tg : ∀ {i : index} {f g : Obj}
      (composable_gf : g sc_is_tg[i] f),
    tg i (g ♯[i] f ← composable_gf) = tg i g
  comp_sc_is_id : ∀ {i : index} {f : Obj},
    f ♯[i] (sc i f) ← idemp_tg_sc.symm = f
  comp_tg_is_id : ∀ {i : index} {f : Obj},
    (tg i f) ♯[i] f ← idemp_sc_tg = f
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
  idemp_sc : ∀ {k : index} {j : Fin k} {f : Obj},
    sc k (sc j f) = sc j f ∧
    sc j f = sc j (sc k f) ∧
    sc j (sc k f) = sc j (tg k f)
  idemp_tg : ∀ {k : index} {j : Fin k} {f : Obj},
    tg k (tg j f) = tg j f ∧
    tg j f = tg j (tg k f) ∧
    tg j (tg k f) = tg j (sc k f)
  sc_comp_is_comp_sc : ∀ {k : index} {j : Fin k} {f g : Obj}
      (composable_j_gf : g sc_is_tg[(j : index)] f),
    sc k (g ♯[(j : index)] f ← composable_j_gf)
    = (sc k g) ♯[(j : index)] (sc k f) ← (by sorry)
  tg_comp_is_comp_tg : ∀ {k : index} {j : Fin k} {f g : Obj}
      (composable_j_gf : g sc_is_tg[(j : index)] f),
    tg k (g ♯[(j : index)] f ← composable_j_gf)
    = (tg k g) ♯[(j : index)] (tg k f) ← (by sorry)
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
