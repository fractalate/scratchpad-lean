-- Practice Session - May 22, 2024

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open BigOperators

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro
  intro xufug

  rw[Set.mem_sUnion] at xufug
  obtain ⟨t, ht⟩ := xufug
  rw[Set.mem_union] at ht
  rw[Set.mem_union, Set.mem_sUnion, Set.mem_sUnion]
  by_cases h : t ∈ F
  apply Or.inl
  use t
  exact And.intro h ht.right
  obtain ⟨tfg, xt⟩ := ht
  rcases tfg
  contradiction
  apply Or.inr
  use t

  intro xfug
  rw[Set.mem_union, Set.mem_sUnion, Set.mem_sUnion] at xfug
  rw[Set.mem_sUnion]
  rcases xfug with xf | xg
  obtain ⟨t, ht⟩ := xf
  use t
  rw[Set.mem_union]
  exact And.intro (Or.inl ht.left) ht.right
  obtain ⟨t, ht⟩ := xg
  use t
  rw[Set.mem_union]
  exact And.intro (Or.inr ht.left) ht.right

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  intro h3
  apply h3 at h1
  contradiction

/-
example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  apply Iff.intro

  intro xab
  rw[Set.mem_sInter]
  intro t tab
  rcases tab with ta | tb
  rw[← ta] at xab
  exact xab.left
  rw[← tb] at xab
  exact xab.right

  intro xab
  rw[Set.mem_sInter] at xab
  have h4 := (xab A) A
  have h5 := (xab B) B
  exact ⟨h4, h5⟩
-/

-- Practice Session - May 23, 2024

-- From a chatter on Twitch on DonDoesMath's channel.
example (m n : ℤ) : (2*m + 1)^2 - (2*n - 1)^2 = 4 * (m + n)*(m - n + 1) := by
  ring

-- Practice Session - May 26, 2024

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  exact h2 (h1 h3)

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x xa
  use A

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x xff
  obtain ⟨t, ⟨tf, xt⟩⟩ := xff
  apply h1 at tf
  use t

example (A : Set U) : A ⊆ A := by
  intro x xa
  assumption

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xab
  exact xab.left

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl A, ← compl_compl B]
  rw[← Set.compl_union]
  rw[compl_compl, compl_compl, compl_compl]

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x
  rw[Set.mem_sInter]
  rw[Set.mem_sInter]
  intro h
  intro t tf
  apply h1 at tf
  apply h at tf
  assumption

example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw[← Nat.even_iff_not_odd]
  unfold Even
  use n

example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) (h₃ : n ≠ 5) : 1 < n := by
  linarith

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  tauto

example (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_succ]; simp
    rw[sum_add_distrib]; simp
    rw[Nat.mul_add]
    rw[n_ih]
    rw[Nat.succ_eq_add_one]
    ring

example (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  apply Iff.intro
  intro xac
  assumption
  intro xac
  assumption

example (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) = ∑ j : Fin m, ∑ i : Fin n, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) := by
  rw[sum_comm]

example (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  induction n
  simp
  rw[sum_add_distrib]
  simp
  ring

example (A B : Prop) (h : A) (hAB : A → B) : B := by
  apply hAB at h
  assumption

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  omega

example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  tauto

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  exact ⟨h1, h2⟩

example (A B C : Prop) : ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

example {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hx
  apply h1 at hx
  apply h2 at hx
  assumption

-- Practice Session - May 27, 2024

example (A B : Prop) (hB : B) : A → (A ∧ B) := by
  intro hA
  exact ⟨hA, hB⟩

example (A : Prop) : ¬A ∨ A := by
  by_cases a : A
  exact Or.inr a
  exact Or.inl a

example (n : ℕ) (h : Odd (n ^ 2)): Odd n := by
  contrapose h
  revert h
  rw[Nat.odd_iff_not_even]
  rw[Nat.odd_iff_not_even]
  push_neg
  unfold Even
  intro h
  obtain ⟨r, hr⟩ := h
  use 2*r^2
  rw[hr]
  ring

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  apply h1 at h2
  assumption

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  apply Iff.intro

  intro xab
  obtain xa | xb := xab
  use A
  exact ⟨Or.inl rfl, xa⟩
  use B
  exact ⟨Or.inr rfl, xb⟩

  intro xab
  obtain ⟨t, th⟩ := xab
  obtain ta | tb := th.left
  rw[ta] at th
  exact Or.inl th.right
  rw[tb] at th
  exact Or.inr th.right

example (A : Set U) (F G : Set (Set U)) (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro x xgg
  by_cases h : x ∈ A
  exact Or.inl h
  apply Or.inr
  intro t tf
  apply h1 at tf
  apply xgg at tf
  obtain xa | xt := tf
  contradiction
  assumption

example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  tauto

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro aiffb
  rw[aiffb]
  simp

example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  contradiction

example (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  rw[Set.inter_union_distrib_left]

example (n : ℕ) (h : n ≠ n) : n = 37 := by
  contradiction

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x xf
  apply xf at h1
  assumption

example (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rw[← h₂]
  rw[h₃]
  rw[← h₁]

example (A B : Set U) : B ⊆ A ∪ B := by
  intro x xb
  exact Or.inr xb

example (A B : Prop) (hA : A) (h : A → B) : B := by
  apply h at hA
  assumption

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  exact h.right

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

example (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  induction m with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[Fin.sum_univ_castSucc (n := n + 1)]
    simp
    rw[n_ih]
    rw[add_pow_two]
    rw[arithmetic_sum]
    ring

example (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  rw[Set.union_comm]

example (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  rw[Set.inter_comm]

example (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  rw[Set.union_inter_distrib_left]

-- Practice Session - May 28, 2024

example (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  unfold Even
  unfold Even at h
  obtain ⟨r, hr⟩ := h
  use 2*r^2
  rw[hr]
  ring

example (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  apply h at k₁
  contradiction

example (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  rw[h] at g
  assumption

example (A : Prop) (hA : A) : A := by
  assumption

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  push_neg
  rfl

example {A : Type} (x : A) : x ∉ (∅ : Set A) := by
  simp

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro

  intro xfug
  obtain ⟨T, hT⟩ := xfug
  obtain TF | TG := hT.left
  apply Or.inl
  use T
  exact ⟨TF, hT.right⟩
  apply Or.inr
  use T
  exact ⟨TG, hT.right⟩

  intro xfxg
  obtain xf | xg := xfxg
  obtain ⟨T, hT⟩ := xf
  use T
  exact ⟨Or.inl hT.left, hT.right⟩
  obtain ⟨T, hT⟩ := xg
  use T
  exact ⟨Or.inr hT.left, hT.right⟩

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  rw[← compl_compl (Aᶜ ∩ Bᶜ)]
  rw[Set.compl_inter Aᶜ Bᶜ]
  rw[compl_compl, compl_compl]

example (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  ext x
  apply Iff.intro

  intro xfg
  constructor
  intro t tf
  have h2 : t ∈ F ∪ G := Or.inl tf
  apply xfg at h2
  assumption
  intro t tg
  have h2 : t ∈ F ∪ G := Or.inr tg
  apply xfg at h2
  assumption

  intro xfg
  intro t tfg
  obtain tf | tg := tfg
  apply xfg.left at tf
  assumption
  apply xfg.right at tg
  assumption

-- Practice Session - May 29, 2024

example : 42 = 42 := by
  rfl

example (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  exact h.right.left

example {A : Type} (x : A) : x ∈ (Set.univ : Set A) := by
  simp

example (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.inter_comm

example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
  rfl

example (n : ℕ) (h : Odd (n ^ 2)) : Odd n := by
  revert h
  contrapose
  rw[← Nat.even_iff_not_odd, ← Nat.even_iff_not_odd]
  unfold Even
  intro er
  obtain ⟨r, hr⟩ := er
  use 2*r^2
  rw[hr]
  ring

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  rw [@Set.sUnion_subset_iff]

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro

  intro ufa
  intro S SF x xS
  have h : x ∈ ⋃₀ F := by use S
  apply ufa at h
  assumption

  intro SFSA
  intro x xf
  rw[Set.mem_sUnion] at xf
  obtain ⟨s, ⟨sf, xs⟩⟩ := xf
  apply SFSA at sf
  apply sf at xs
  assumption

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro

  intro fa
  intro s sf x xs
  have h : x ∈ ⋃₀ F := by use s
  apply fa at h
  assumption

  intro sfsa
  intro x xf
  rw[Set.mem_sUnion] at xf
  obtain ⟨s, ⟨sf, xs⟩⟩ := xf
  apply sfsa at sf
  apply sf at xs
  assumption

-- Practice Session - May 30, 2024

example (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
  linarith

example (A : Set ℕ) : A ⊆ Set.univ := by
  intro x
  simp

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro

  intro x s sf
  simp at x
  apply x at sf
  assumption

  intro sfsa x xf
  obtain ⟨t, ⟨tf, xt⟩⟩ := xf
  apply sfsa at tf
  apply tf at xt
  assumption

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x

  apply Iff.intro
  intro ⟨xa, u, uf, xu⟩
  simp
  use A ∩ u
  constructor
  use u
  exact ⟨xa, xu⟩

  intro ⟨u, ⟨s, sf, uas⟩, xu⟩
  rw[uas] at xu
  constructor
  exact xu.left
  use s
  exact ⟨sf, xu.right⟩

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  apply Iff.intro

  intro ⟨xa, t, tf, xt⟩
  use A ∩ t
  constructor
  use t
  exact ⟨xa, xt⟩

  intro ⟨t, ⟨s, sf, tas⟩, xt⟩
  rw[tas] at xt
  constructor
  exact xt.left
  use s
  exact ⟨sf, xt.right⟩
