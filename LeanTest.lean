-- This module serves as the root of the `LeanTest` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

theorem one_equals_one : 1 = 1 := by
  rfl

theorem x_in_A (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h
example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  -- Must satisfy all arguments to the theorem being referenced.
  have h3 : x ∈ A := x_in_A x A h2
  exact h1 h3

-- --------------------------------- --
--      Subset World - Level 1       --
-- --------------------------------- --

example (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h

-- --------------------------------- --
--      Subset World - Level 2       --
-- --------------------------------- --

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

-- --------------------------------- --
--      Subset World - Level 3       --
-- --------------------------------- --
example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  -- alternate proof
  --have h4 : x ∈ B := h1 h3
  --exact h2 h4
  exact h2 (h1 h3)

-- --------------------------------- --
--      Subset World - Level 4       --
-- --------------------------------- --
example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  intro h3 -- x ∈ A
  have h4 : x ∈ B := h1 h3
  exact h2 h4

-- Reordering "the things" at the start doesn't seem to matter.
example {x : U} {A B C : Set U} (h2 : x ∈ B → x ∈ C) (h1 : A ⊆ B) : x ∈ A → x ∈ C := by
  intro h3 -- x ∈ A
  have h4 : x ∈ B := h1 h3
  exact h2 h4

-- This is a nonsense example to illustrate binders.
-- "Binders" appear to come from the kind of goal you are working toward.
example {x : U} {A B C : Set U} (h2 : B ⊆ C) /-(h1 : A ⊆ B)-/ : (x ∈ A) ∧ (x ∈ B) → x ∈ C := by
  intro h3 -- (x ∈ A) ∧ (x ∈ B)
  exact h2 (And.right h3)

-- --------------------------------- --
--      Subset World - Level 5       --
-- --------------------------------- --
theorem Subset.refl (A : Set U) : A ⊆ A := by
  intro x -- Notice how this intro works differently than the next one. This appears to rewrite the goal.
  intro h1 -- And this appears to introduce an assumption.
  exact h1

theorem Subset.refl2 {x : U} (A : Set U) : x ∈ A → x ∈ A := by
  intro h1
  exact h1

-- --------------------------------- --
--      Subset World - Level 6       --
-- --------------------------------- --
theorem Subset.trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x -- x : U . Goal is rewritten to x ∈ A → x ∈ C .
  intro xinA -- x ∈ A from the revised goal
  --        V ---- here's the conclusion that is introduced as h3
  have h3 : x ∈ B := h1 xinA
  exact h2 h3

theorem Subset.trans2 {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x -- x : U . Goal is rewritten to x ∈ A → x ∈ C .
  intro xinA -- x ∈ A from the revised goal
  exact h2 (h1 xinA)

#check Subset.trans


-- --------------------------------- --
--    Complement World - Level 1     --
-- --------------------------------- --
example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  intro h3
  have h4 : x ∈ B := h3 h1
  exact h2 h4

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra h3 -- TODO: In what cases does by_contra differ from intro in Lean 4?
  have h4 : x ∈ B := h3 h1
  exact h2 h4

-- --------------------------------- --
--    Complement World - Level 2     --
-- --------------------------------- --
theorem mem_compl_iff2 (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

theorem mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  exact mem_compl_iff2 A x


-- --------------------------------- --
--    Complement World - Level 3     --
-- --------------------------------- --
theorem compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rewrite [mem_compl_iff A x]
  rewrite [mem_compl_iff B x] at h2
  by_contra h3
  have h4 : x ∈ B := h1 h3
  exact h2 h4

theorem compl_subset_compl_of_subset2 {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x h2
  rewrite [mem_compl_iff A x]
  rewrite [mem_compl_iff B x] at h2
  intro h3 -- Notice that this proof is valid too, differing from the previous usage of by_contra
  have h4 : x ∈ B := h1 h3
  exact h2 h4

theorem mem_compl_imp (A : Set U) (x : U) : x ∈ Aᶜ → x ∉ A := by
  intro h2
  exact h2

-- You can also prove this without rewrites!!!!
theorem compl_subset_compl_of_subset3 {A B : Set U} (h1 : A ⊆ B): Bᶜ ⊆ Aᶜ := by
  intro x h2
  have h3 : x ∉ B := h2
  intro h4
  have h5 : x ∈ B := h1 h4
  exact h3 h5

-- Here's a shorter proof without rewrites!!
theorem compl_subset_compl_of_subset4 {A B : Set U} (h1 : A ⊆ B): Bᶜ ⊆ Aᶜ := by
  intro x h2 h3
  have h4 : x ∈ B := h1 h3
  exact h2 h4

-- --------------------------------- --
--    Complement World - Level 4     --
-- --------------------------------- --
theorem compl_compl2 (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  intro x
  intro xinA
  rewrite [mem_compl_iff Aᶜ x] at xinA
  rewrite [mem_compl_iff A x] at xinA
  push_neg at xinA
  exact xinA
  intro x xinA
  rewrite [mem_compl_iff Aᶜ x]
  rewrite [mem_compl_iff A x]
  push_neg
  exact xinA

-- We should use that built-in!
theorem compl_compl3 (A : Set U) : Aᶜᶜ = A := by
  exact compl_compl A

-- Intermediate stage of rewriting this with fewer rewrites.
theorem compl_compl4 (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  intro x xinA
  rewrite [mem_compl_iff Aᶜ x] at xinA
  have xinA : ¬x ∉ A := xinA
  push_neg at xinA
  exact xinA
  intro x xinA
  rewrite [mem_compl_iff Aᶜ x]
  rewrite [mem_compl_iff A x]
  push_neg
  exact xinA

theorem compl_compl5 (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  intro x xinA
  rewrite [mem_compl_iff Aᶜ x] at xinA
  have xinA : ¬x ∉ A := xinA
  push_neg at xinA
  exact xinA
  intro x xinA
  rewrite [mem_compl_iff Aᶜ x]
  rewrite [mem_compl_iff A x]
  push_neg
  exact xinA

-- --------------------------------- --
--    Complement World - Level 5     --
-- --------------------------------- --
example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro

  intro h1
  exact compl_subset_compl_of_subset h1

  intro h1
  apply compl_subset_compl_of_subset at h1
  rw [compl_compl] at h1
  rw [compl_compl] at h1
  exact h1


-- --------------------------------- --
--   Intersection World - Level 1    --
-- --------------------------------- --
example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

-- --------------------------------- --
--   Intersection World - Level 2    --
-- --------------------------------- --
example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  rewrite [Set.mem_inter_iff x A B] at h
  exact h.right

-- Without the rewrite.
example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  have h2 : x ∈ A ∧ x ∈ B := h
  exact h2.right

-- And it seems to understand this also, automatically pulling out x ∈ B from the intersection.
example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  exact h.right

-- --------------------------------- --
--   Intersection World - Level 3    --
-- --------------------------------- --
example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xAB
  exact xAB.left

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xAB
  have h2 : x ∈ A ∧ x ∈ B := xAB
  exact h2.left

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xAB
  rewrite [Set.mem_inter_iff x A B] at xAB
  exact xAB.left

-- --------------------------------- --
--   Intersection World - Level 4    --
-- --------------------------------- --
example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  exact And.intro h1 h2

-- --------------------------------- --
--   Intersection World - Level 5    --
-- --------------------------------- --
example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x xA
  have xB : x ∈ B := h1 xA
  have xC : x ∈ C := h2 xA
  exact And.intro xB xC

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x
  intro xA
  rewrite [Set.mem_inter_iff x B C]
  exact And.intro (h1 xA) (h2 xA)

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x
  intro xA
  rewrite [Set.mem_inter_iff x B C]
  exact And.intro (h1 xA) (h2 xA)

-- --------------------------------- --
--   Intersection World - Level 6    --
-- --------------------------------- --
theorem inter_subset_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x xAB
  exact And.intro xAB.right xAB.left

-- With rewrites.
theorem inter_subset_swap2 (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x xAB
  rewrite [Set.mem_inter_iff x B A]
  rewrite [Set.mem_inter_iff x A B] at xAB
  exact And.intro xAB.right xAB.left

-- --------------------------------- --
--   Intersection World - Level 7    --
-- --------------------------------- --
theorem inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.Subset.antisymm
  intro x xAB
  exact And.intro xAB.right xAB.left
  intro x xAB
  exact And.intro xAB.right xAB.left

-- Using the previous leve's theorems.
theorem inter_comm2 (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.Subset.antisymm
  exact inter_subset_swap A B
  exact inter_subset_swap B A

-- --------------------------------- --
--   Intersection World - Level 8    --
-- --------------------------------- --
theorem inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  apply Iff.intro

  intro xABC
  have xABC : (x ∈ A ∧ x ∈ B) ∧ x ∈ C := xABC
  have xAB : x ∈ A ∧ x ∈ B := xABC.left
  have xC : x ∈ C := xABC.right
  exact And.intro xAB.left (And.intro xAB.right xC)

  intro xABC
  have xABC : x ∈ A ∧ (x ∈ B ∧ x ∈ C) := xABC
  have xA : x ∈ A := xABC.left
  have xBC : x ∈ B ∧ x ∈ C := xABC.right
  exact And.intro (And.intro xA xBC.left) xBC.right

theorem inter_assoc2 (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  apply Iff.intro

  intro xABC
  rewrite [Set.mem_inter_iff]
  rewrite [Set.mem_inter_iff]
  rewrite [Set.mem_inter_iff] at xABC
  rewrite [Set.mem_inter_iff] at xABC
  have xA : x ∈ A := xABC.left.left
  have xB : x ∈ B := xABC.left.right
  have xC : x ∈ C := xABC.right
  exact And.intro xA (And.intro xB xC)

  intro xABC
  rewrite [Set.mem_inter_iff]
  rewrite [Set.mem_inter_iff]
  rewrite [Set.mem_inter_iff] at xABC
  rewrite [Set.mem_inter_iff] at xABC
  have xA : x ∈ A := xABC.left
  have xB : x ∈ B := xABC.right.left
  have xC : x ∈ C := xABC.right.right
  exact And.intro (And.intro xA xB) xC

-- Lean will figure out a bunch of this stuff for you.
theorem inter_assoc3 (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  apply Iff.intro

  intro xABC
  exact And.intro xABC.left.left (And.intro xABC.left.right xABC.right)

  intro xABC
  exact And.intro (And.intro xABC.left xABC.right.left) xABC.right.right
