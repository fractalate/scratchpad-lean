import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open Fintype
open BigOperators

-- Practice Session - June 3, 2024

example (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) = ∑ j : Fin m, ∑ i : Fin n, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) := by
  rw [@sum_comm]

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  apply Iff.intro

  intro ⟨xa, ⟨t, ⟨tf, xt⟩⟩⟩
  use A ∩ t
  constructor
  use t
  exact ⟨xa, xt⟩

  intro ⟨t, ⟨⟨u, ⟨uf, tau⟩⟩, xt⟩⟩
  rw[tau] at xt
  constructor
  exact xt.left
  use u
  exact ⟨uf, xt.right⟩
