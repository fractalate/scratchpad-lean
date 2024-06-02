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
  use {default}
  use {default}
  use {}
  simp

theorem MunkresCh1Ex2PartB {U} [h : Nontrivial U] : ∃ (A B C : Set U), ¬(A ⊆ B ∨ A ⊆ C ↔ A ⊆ (B ∪ C)) := by
  obtain ⟨b, ⟨c, hc⟩⟩ := h
  use {b, c}, {b}, {c}
  simp
  rw[ne_eq, ←false_iff, iff_comm] at hc
  rw[eq_comm, hc]; simp
  rw[Set.pair_comm]
