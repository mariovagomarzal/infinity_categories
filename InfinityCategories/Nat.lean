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

instance : SingleSortedCategory (Nat×Nat) where
  sc := fun _ (_, y₂) ↦ (y₂, y₂)
  tg := fun _ (x₁, _) ↦ (x₁, x₁)
  pcomp := fun _ (y₁, y₂) (x₁, x₂) ↦ ⟨y₂ = x₁, fun _ ↦ (y₁, x₂)⟩
  pcomp_dom := by
    intros
    apply Iff.intro
    · intros
      simpa
    · intro h
      simp at h
      simpa
  idemp_sc_sc := by intros; rfl
  idemp_tg_sc := by intros; rfl
  idemp_sc_tg := by intros; rfl
  idemp_tg_tg := by intros; rfl
  sc_comp_is_sc := by intros; rfl
  tg_comp_is_tg := by intros; rfl
  comp_sc_is_id := by intros; rfl
  comp_tg_is_id := by intros; rfl
  assoc := by intros; rfl

end SingleSortedCategories
