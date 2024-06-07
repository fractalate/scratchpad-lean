-- Munkres, Topology (2nd Edition)
-- Exercises from Chapter 1

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset


---------------------------
-- Chapter 1, Exercise 1 --
---------------------------

-- Distributive Laws for ∪ and ∩

theorem MunkresCh1Ex1PartA {U} (A B C : Set U) : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  apply Iff.intro

  intro xabc
  obtain xb | xc := xabc.right
  exact Or.inl ⟨xabc.left, xb⟩
  exact Or.inr ⟨xabc.left, xc⟩

  intro xabac
  obtain xab | xac := xabac
  exact ⟨xab.left, Or.inl xab.right⟩
  exact ⟨xac.left, Or.inr xac.right⟩

theorem MunkresCh1Ex1PartB {U} (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro

  intro xabc
  obtain xa | xbc := xabc
  exact ⟨Or.inl xa, Or.inl xa⟩
  exact ⟨Or.inr xbc.left, Or.inr xbc.right⟩

  intro xabac
  obtain ⟨xab, xac⟩ := xabac
  rcases xab with xa | xb
  exact Or.inl xa
  rcases xac with xa | xc
  exact Or.inl xa
  exact Or.inr ⟨xb, xc⟩

-- DeMorgan's Laws

theorem MunkresCh1Ex1PartC {U} (A B C : Set U) : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  ext x
  apply Iff.intro

  intro xabc
  obtain ⟨xa, xmbc⟩ := xabc
  rw [← Set.mem_compl_iff, Set.compl_union] at xmbc
  constructor
  use xa
  exact xmbc.left
  use xa
  exact xmbc.right

  intro xabac
  obtain ⟨xab, xac⟩ := xabac
  constructor
  exact xab.left
  rw [← Set.mem_compl_iff, Set.compl_union]
  exact ⟨xab.right, xac.right⟩

theorem MunkresCh1Ex1PartD {U} (A B C : Set U) : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  ext x
  apply Iff.intro

  intro xabc
  obtain ⟨xa, xnbc⟩ := xabc
  rw [← Set.mem_compl_iff, Set.compl_inter] at xnbc
  obtain xnb | xnc := xnbc
  exact Or.inl ⟨xa, xnb⟩
  exact Or.inr ⟨xa, xnc⟩

  intro xabac
  obtain xab | xac := xabac
  constructor
  exact xab.left
  rw [← Set.mem_compl_iff, Set.compl_inter]
  exact Or.inl xab.right
  constructor
  exact xac.left
  rw [← Set.mem_compl_iff, Set.compl_inter]
  exact Or.inr xac.right


---------------------------
-- Chapter 1, Exercise 2 --
---------------------------

-- The statement
--   A ⊆ B ∧ A ⊆ C ↔ A ⊆ (B ∪ C)
-- is not generally true; for example, if
--   A = {x}
--   B = {x}
--   and C = {}
-- we have A ⊆ (B ∪ C), but ¬(A ⊆ C).
theorem MunkresCh1Ex2PartA {U} [Inhabited U] : ∃ A B C : Set U, ¬(A ⊆ B ∧ A ⊆ C ↔ A ⊆ (B ∪ C)) := by
  use {default}, {default}, {}
  simp

-- The statement
--   A ⊆ B ∨ A ⊆ C ↔ A ⊆ (B ∪ C)
-- is not generally true; for example, if
--   A = {b, c}
--   B = {b}
--   C = {c}
-- we have A ⊆ (B ∪ C), but ¬(A ⊆ B ∨ A ⊆ C).
theorem MunkresCh1Ex2PartB {U} [h : Nontrivial U] : ∃ (A B C : Set U), ¬(A ⊆ B ∨ A ⊆ C ↔ A ⊆ (B ∪ C)) := by
  obtain ⟨b, ⟨c, hc⟩⟩ := h
  use {b, c}, {b}, {c}
  simp
  rw[ne_eq, ←false_iff, iff_comm] at hc
  rw[eq_comm, hc]; simp
  rw[Set.pair_comm]

theorem MunkresCh1Ex2PartC {U} (A B C : Set U) : A ⊆ B ∧ A ⊆ C ↔ A ⊆ (B ∩ C) := by
  rw [@Set.subset_inter_iff]

-- The statement
--   A ⊆ B ∨ A ⊆ C ↔ A ⊆ (B ∩ C)
-- is not generally true; for example, if
--   A = {x}
--   B = {}
--   C = {x}
-- we have (A ⊆ B ∨ A ⊆ C), but ¬(A ⊆ (B ∩ C)).
theorem MunkresCh1Ex2PartD {U} [Inhabited U] : ∃ A B C : Set U, ¬(A ⊆ B ∨ A ⊆ C ↔ A ⊆ (B ∩ C)) := by
  use {default}, {}, {default}
  simp

-- The statement
--   A \ (A \ B) = B
-- is not generally true; for example, if
--   A = {}
--   B = {x}
-- we have A \ (A \ B) = ∅ and B ≠ ∅.
theorem MunkresCh1Ex2PartE {U} [Inhabited U] : ∃ A B : Set U, ¬(A \ (A \ B) = B) := by
  use {}, {default}
  simp
  push_neg
  unfold Set.Nonempty
  by_contra h
  push_neg at h
  have h2 := h default
  apply h2
  simp

-- However, the statement in part E becomes true when = is replaced by ⊆.
theorem MunkresCh1Ex2PartE2 {U} (A B : Set U) : A \ (A \ B) ⊆ B := by
  intro x
  rw[Set.diff_eq, Set.diff_eq]
  rw[Set.compl_inter, compl_compl]
  rw[Set.inter_union_distrib_left, Set.inter_compl_self]
  simp

-- The statement
--   A \ (B \ A) = A \ B
-- is not generally true; for example, if
--   A = {x}
--   B = {x}
-- Then A \ (B \ A) = {x}, but A \ B = ∅ ≠ {x}.
theorem MunkresCh1Ex2PartF {U} [Inhabited U] : ∃ (A B : Set U), ¬(A \ (B \ A) = A \ B) := by
  use {default}, {default}
  simp

-- However, the statement in part F becomes true when the equation is
-- reversed and = is replaced by ⊆.
theorem MunkresCh1Ex2PartF2 {U} (A B : Set U) : A \ B ⊆ A \ (B \ A) := by
  intro x ⟨xa, xb⟩
  constructor
  assumption
  rw [@Set.mem_diff]
  push_neg
  intro oops
  contradiction

theorem MunkresCh1Ex2PartG {U} (A B C : Set U) : A ∩ (B \ C) = (A ∩ B) \ (A ∩ C) := by
  ext x
  apply Iff.intro

  intro ⟨xa, xb, xc⟩
  simp
  constructor
  exact ⟨xa, xb⟩
  intro
  assumption

  intro ⟨⟨xa, xb⟩, xc⟩
  rw[← Set.mem_compl_iff, Set.compl_inter] at xc
  obtain xa | xc := xc
  contradiction
  simp
  exact ⟨xa, xb, xc⟩

  -- Or more simply, just:
  --rw [@Set.inter_diff_distrib_left]
