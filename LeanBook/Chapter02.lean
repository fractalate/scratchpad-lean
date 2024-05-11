-- Theorem Proving in Lean 4
-- Notes from Chapter 2
-- https://leanprover.github.io/theorem_proving_in_lean4/dependent_type_theory.html
-- May 8, 2024

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open BigOperators

-- You can define constants in this way.
-- "def" is the operative word. This is similar to the
-- "have" syntax.
def favorite_number : Nat := 6
def theorem_valid : Bool := true -- false is the other value.

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m            -- output: Nat
#check n
#check n + 0        -- Nat
#check m * (n + 0)  -- Nat
#check b1           -- Bool
#check b1 && b2     -- "&&" is the Boolean and
#check b1 || b2     -- Boolean or
#check true         -- Boolean "true"
#check false        -- Boolean "false"

theorem one_eq_one : 1 = 1 := by rfl
#check one_eq_one

/- Evaluate -/

#eval 5 * 4         -- 20
#eval m + 2         -- 3
#eval b1 && b2      -- false

/- Use \times to create the × symbol, which stands for
   cartesian product and values of that type are denoted
   with pairs in parenthesis: (a, b).  -/

def value1 : Nat := 10
def value2 : Nat := 11
def pair : Nat × Nat := (value1, value2)

/-
Think of Type 0 as a universe of "small" or "ordinary" types. Type 1 is then a larger universe of types, which contains Type 0 as an element, and Type 2 is an even larger universe of types, which contains Type 1 as an element. The list is indefinite, so that there is a Type n for every natural number n. Type is an abbreviation for Type 0:
-/
#check Type      -- Type 1
#check Type 0    -- Type 1
#check Type 1    -- Type 2
#check Type 2    -- Type 3
#check Type 3    -- Type 4
#check Type 4    -- Type 5


def F.{u} (α : Type u) : Type u := Prod α α

#check F    -- Type u → Type u

-- My first definiiton.
def plus_one (a : Nat) := a + 1
-- Proof of my first definition.
example (a : Nat) : plus_one a = Nat.succ a := by
   trivial

def plus_two := λ (x : Nat) => x + 2

example (a : Nat) : plus_two a = Nat.succ (Nat.succ a) := by
   trivial

def collatz (a : Nat) :=  if a % 2 == 0 then a / 2 else 2 * n + 1

def add_two_things (a b : Int):= a + b
example (a b : Int) : add_two_things a b = add_two_things b a := by
   rw[add_two_things]
   rw[add_two_things]
   ring


def my_succ : Int -> Int := add_two_things 1
#eval my_succ 10
example (a : Int) : my_succ a = Int.succ a := by
   rw[my_succ]
   rw[add_two_things]
   rw[Int.succ]
   ring


universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2
def h1_2 (x : Nat) : Type :=
  (f Type (fun α => α) Nat x).1
def h1_3 (x : Nat) :=
  (f Type (fun α => α) Nat x)

#eval h1 5 -- 5
#check h1_2 5 -- Type

#check id h1_2 2
#check id (h1_3 1).2

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5

#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat
