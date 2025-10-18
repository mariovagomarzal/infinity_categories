/-
Copyright (c) 2025 Mario Vago Marzal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enric Cosme Llópez, Raul Ruiz Mora, Mario Vago Marzal
-/
import InfinityCategories.SingleSortedCategories.Basic

/-!
TODO: Document the file.
-/

namespace SingleSortedCategories

instance : SingleSortedCategory Unit where
  sc _ _ := ()
  tg _ _ := ()
  pcomp _ _ _ := ⟨True, (fun _ ↦ ())⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      rfl
    · intros
      trivial
  scsc := by intros; rfl
  tgsc := by intros; rfl
  sctg := by intros; rfl
  tgtg := by intros; rfl
  sc_comp_is_sc := by intros; rfl
  tg_comp_is_tg := by intros; rfl
  comp_sc_is_id := by intros; rfl
  comp_tg_is_id := by intros; rfl
  assoc := by intros; rfl

end SingleSortedCategories
