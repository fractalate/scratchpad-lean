-- Practice Session - May 18, 2024

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open BigOperators

example (A : Set U) : ∃ s, s ⊆ A := by
  use A

example (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  induction n
  simp
  rw[sum_add_distrib]
  simp
  ring

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

example (A : Set U) (F G : Set (Set U)) (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro x
  rw[Set.mem_sInter]
  rw[Set.mem_union]
  rw[Set.mem_sInter]
  intro htg
  by_cases d : x ∈ A
  exact Or.inl d
  apply Or.inr
  intro t tf
  apply h1 at tf
  apply htg at tf
  rcases tf with xa | xt
  contradiction
  assumption

example (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  apply Iff.intro

  intro ab
  intro notb
  by_contra a
  apply ab at a
  contradiction

  intro nbna
  intro a
  by_contra b
  apply nbna at b
  contradiction

example (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[n_ih]
    rw[Nat.succ_eq_add_one]
    ring

example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
  apply Iff.intro
  intro mn
  linarith
  intro mn
  linarith

example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
  rfl

example (n : ℕ) : (∑ i : Fin n, (0 + 0)) = 0 := by
  induction n
  simp
  rw[Fin.sum_const]
  ring

theorem inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  apply Iff.intro

  intro xabc
  exact ⟨xabc.left.left, ⟨xabc.left.right, xabc.right⟩⟩
  intro xabc
  exact ⟨⟨xabc.left, xabc.right.left⟩, xabc.right.right⟩

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  rw[Set.mem_sUnion]
  apply Iff.intro

  intro xaub
  rcases xaub with xa | xb
  use A
  constructor
  simp
  assumption
  use B
  constructor
  simp
  assumption

  intro htab
  rcases htab with ⟨t, ht⟩
  rcases ht with ⟨tisa | tisb, xt⟩
  rw[tisa] at xt
  exact Or.inl xt
  rw[tisb] at xt
  exact Or.inr xt

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  rw[Set.mem_union]
  rw[Set.mem_sUnion]
  apply Iff.intro

  intro tfug
  rcases tfug with ⟨t, hxt⟩
  rcases hxt with ⟨tf | tg, xt⟩
  apply Or.inl
  use t
  apply Or.inr
  use t

  intro xufxug
  rcases xufxug with xuf | xug
  rcases xuf with ⟨S, hS⟩
  use S
  exact ⟨Or.inl hS.left, hS.right⟩
  rcases xug with ⟨S, hS⟩
  use S
  exact ⟨Or.inr hS.left, hS.right⟩

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

example : True := by
  trivial

example (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[Nat.succ_eq_add_one]
    rw[mul_add]
    rw[n_ih]
    ring

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  rw[Set.mem_union]
  rw[Set.mem_sUnion]
  rw[Set.mem_sUnion]
  rw[Set.mem_sUnion]
  apply Iff.intro

  intro tfug
  rcases tfug with ⟨t, tfgxt⟩
  rcases tfgxt with ⟨h | h, tf⟩
  apply Or.inl
  use t
  apply Or.inr
  use t

  intro tfug
  rcases tfug with tf | tg
  rcases tf with ⟨t, th⟩
  use t
  exact ⟨Or.inl th.left, th.right⟩
  rcases tg with ⟨t, th⟩
  use t
  exact ⟨Or.inr th.left, th.right⟩

-- Practice Session - May 20, 2024

example (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  exact Or.inl hA

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  rcases h with ab | a
  exact ab.left
  exact a

example (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  apply Iff.intro

  intro aff
  intro s sf
  intro x h
  apply aff at h
  rw[Set.mem_sInter] at h
  apply h at sf
  assumption

  intro fasf
  intro x xa
  rw[Set.mem_sInter]
  intro t h
  apply fasf at h
  apply h at xa
  assumption

example (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) = ∑ j : Fin m, ∑ i : Fin n, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) := by
  rw[sum_comm]

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  unfold Odd at h
  unfold Odd
  rcases h with ⟨k, hk⟩
  use 2*k^2 + 2*k
  rw[hk]
  ring

theorem arithmetic_sum
 (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    ring
    rw[mul_comm]
    rw[Nat.succ_eq_add_one]
    rw[n_ih]
    ring

-- Practice Session - May 21, 2024

example (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  induction m with
  | zero =>
    simp
  | succ n n_ih =>
    rw [Fin.sum_univ_castSucc]
    simp
    rw[n_ih]
    --rw [Fin.sum_univ_castSucc] -- Type specification is necessary.
    rw [Fin.sum_univ_castSucc (n := n + 1)]
    simp
    rw[add_pow_two]
    rw[arithmetic_sum]
    ring

example (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  exact (h k.left) k.right

example (A B C D E F G H I : Prop) (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  intro a
  exact p (l (i (f a)))

example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h: ∀ (y : People), isDrinking y
  use default
  intro
  exact h
  push_neg at h
  obtain ⟨y, hy⟩ := h
  use y
  intro y
  contradiction

example (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  apply Iff.intro
  assumption
  assumption

example (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  induction m with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[n_ih]
    rw[Fin.sum_univ_castSucc (n := n + 1)]
    simp
    rw[add_pow_two]
    rw[arithmetic_sum]
    ring

example (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[Nat.succ_eq_add_one]
    rw[n_ih]
    ring

example (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  apply Iff.intro

  intro ab
  by_cases h : A
  apply ab at h
  exact Or.inr h
  exact Or.inl h

  intro nab
  intro a
  obtain na | b := nab
  contradiction
  assumption

example : ¬False := by
  trivial

example (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  induction m with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[Fin.sum_univ_castSucc (n := n + 1)]
    rw[n_ih]
    simp
    rw[add_pow_two]
    rw[arithmetic_sum]
    ring

-- Practice Session - May 24, 2024

example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  rw[Set.mem_sInter]

  apply Iff.intro
  intro xab
  intro t tab
  rcases tab with xa | xb
  rw[← xa] at xab
  exact xab.left
  rw[← xb] at xab
  exact xab.right

  intro tabxt
  apply And.intro
  apply tabxt
  exact Or.inl rfl
  apply tabxt
  exact Or.inr rfl
