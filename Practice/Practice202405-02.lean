import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open BigOperators

-- Practice Session - May 16, 2024

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x xa
  have h : x ∈ A ∪ C := Or.inl xa
  apply h1 at h
  rcases h with xb | xc
  assumption
  have k : x ∈ A ∩ C := And.intro xa xc
  apply h2 at k
  exact k.left

example (A : Set U) : Aᶜᶜ = A := by
  ext x
  rw[Set.mem_compl_iff]
  apply Iff.intro
  intro xac
  rw[Set.mem_compl_iff] at xac
  push_neg at xac
  assumption
  intro xa
  rw[Set.mem_compl_iff]
  push_neg
  assumption

example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  rw[Set.mem_sInter]
  apply Iff.intro

  intro xab
  intro t tab
  rcases tab with ta | tb
  rcases xab with ⟨xa, xb⟩
  rw[← ta] at xa
  assumption
  rcases xab with ⟨_xa, xb⟩
  rw[← tb] at xb
  assumption

  intro tab
  apply And.intro
  apply tab
  exact Or.inl rfl
  apply tab
  exact Or.inr rfl

example (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  intro a
  rw[h] at a
  apply g at a
  assumption

example (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro

  intro xaubc
  rcases xaubc with a | ⟨b, c⟩
  exact And.intro (Or.inl a) (Or.inl a)
  exact And.intro (Or.inr b) (Or.inr c)

  intro xaubauc
  rcases xaubauc with ⟨ab, ac⟩
  by_cases a : x ∈ A
  exact Or.inl a
  rcases ab with oops | xb
  contradiction
  rcases ac with oops | xc
  contradiction
  exact Or.inr (And.intro xb xc)

example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw[h₁]
  rw[← h₃]
  rw[h₂]

example : 1 + 1 = 2 := by
  linarith

example (A B : Prop) (h : A ↔ B) : B ↔ A := by
  rw[h]

example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  unfold Odd
  unfold Even

  intro x xeven
  rcases xeven with ⟨r, hr⟩
  use r
  rw[hr]
  ring

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x
  rw[Set.mem_sUnion]
  rw[Set.mem_sUnion]
  intro h
  rcases h with ⟨t, th⟩
  rcases th with ⟨tf, xt⟩
  apply h1 at tf
  use t

example (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  apply h at k₁
  contradiction

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x xaub
  rcases xaub with xa | xb
  apply h1 at xa
  assumption
  apply h2 at xb
  assumption

example (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  rw[Set.mem_sInter]
  rw[Set.mem_inter_iff]
  rw[Set.mem_sInter]
  rw[Set.mem_sInter]
  apply Iff.intro

  intro fatfug
  constructor
  intro t tf
  have tfg : t ∈ F ∪ G := Or.inl tf
  apply fatfug at tfg
  assumption
  intro t tg
  have tfg : t ∈ F ∪ G := Or.inr tg
  apply fatfug at tfg
  assumption

  intro h
  rcases h with ⟨fatf, fatg⟩
  intro t tfug
  rcases tfug with tf | tg
  apply fatf at tf
  assumption
  apply fatg at tg
  assumption

example (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  revert h
  contrapose
  rw[Nat.odd_iff_not_even]
  rw[Nat.odd_iff_not_even]
  push_neg
  unfold Even
  intro h1
  rcases h1 with ⟨r, hr⟩
  use 2*r^2
  rw[hr]
  ring

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x
  rw[Set.mem_sUnion]
  rw[Set.mem_sUnion]
  intro tf
  rcases tf with ⟨t, ht⟩
  rcases ht with ⟨tf, xt⟩
  apply h1 at tf
  use t

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  push_neg
  apply Iff.intro
  intro h
  exact h
  intro h
  exact h

example (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n with
  | zero =>
    trivial
  | succ n n_ih =>
    rw[Fin.sum_univ_succ]
    simp
    rw[sum_add_distrib]
    simp
    rw[Nat.mul_add]
    rw[n_ih]
    rw[Nat.succ_eq_add_one]
    ring

example (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  induction n
  trivial
  rw[sum_add_distrib]
  simp
  ring

theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  apply Iff.intro
  intro xabc
  rw[Set.mem_compl_iff] at xabc
  simp at xabc
  by_cases h : x ∈ A
  apply xabc at h
  exact Or.inr h
  exact Or.inl h

  intro xacab
  rcases xacab with ac | ab
  rw[Set.mem_compl_iff]
  simp
  intro xa
  contradiction
  simp
  contrapose
  intro xb
  contradiction

-- Practice Session - May 17, 2024

example (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  by_contra h
  apply g at h
  contradiction

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x xa
  exact And.intro (h1 xa) (h2 xa)

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x
  rw[Set.mem_sUnion]
  rw[Set.mem_sUnion]
  intro th
  rcases th with ⟨t, th⟩
  have tg : t ∈ G := h1 th.left
  use t
  exact And.intro tg th.right

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

example (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
  linarith

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rw[Set.mem_compl_iff]
  apply Iff.intro
  intro xabc
  simp at xabc
  push_neg at xabc
  assumption
  intro xacbc
  simp
  push_neg
  assumption

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

example (n : ℕ) (h : 2 ≤ n) : n ≠ 0 := by
  linarith

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  rw[Set.mem_sUnion]
  apply Iff.intro
  intro xab
  simp
  rcases xab with xa | xb
  exact Or.inl xa
  exact Or.inr xb

  intro h
  rcases h with ⟨t, th⟩
  rcases th with ⟨tab, xt⟩
  rcases tab with ta | tb
  rw[ta] at xt
  exact Or.inl xt
  rw[tb] at xt
  exact Or.inr xt

example (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  revert h
  contrapose
  rw[Nat.odd_iff_not_even]
  rw[Nat.odd_iff_not_even]
  push_neg
  unfold Even
  intro h
  rcases h with ⟨r, hr⟩
  use 2*r^2
  rw[hr]
  ring

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro

  intro h
  intro x xbc
  simp
  by_contra oops
  apply h at oops
  contradiction

  intro h
  simp at h -- :) the other case can be about this small too or the entire proof can be a simp
  assumption

example (n : ℕ) : (∑ i : Fin n, (2 * (i : ℕ) + 1)) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[n_ih]
    rw[Nat.succ_eq_one_add]
    ring

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  rw[Set.mem_sUnion]
  apply Iff.intro

  intro xaub
  rcases xaub with xa | xb
  use A
  simp
  assumption
  use B
  simp
  assumption

  intro h
  rcases h with ⟨t, th⟩
  rcases th with ⟨tab, xt⟩
  rcases tab with ta | tb
  rw[ta] at xt
  exact Or.inl xt
  rw[tb] at xt
  exact Or.inr xt
