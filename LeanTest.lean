-- This module serves as the root of the `LeanTest` library.
-- Import modules here that should be built as part of the library.

import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset
import «LeanBook».Chapter02

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

--#check Subset.trans


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

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  rewrite [Set.mem_inter_iff] at h
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

-- --------------------------------- --
--      Union World - Level 1        --
-- --------------------------------- --
example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

-- Similarly
example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  have h2 : x ∈ A ∨ x ∈ B := Or.inl h
  exact h2

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  apply Or.inl
  exact h

-- --------------------------------- --
--      Union World - Level 2        --
-- --------------------------------- --
example (A B : Set U) : B ⊆ A ∪ B := by
  intro x xB
  apply Or.inr
  exact xB

-- --------------------------------- --
--      Union World - Level 3        --
-- --------------------------------- --
example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x xAB
  have xAB : x ∈ A ∨ x ∈ B := xAB
  cases' xAB with xA xB
  exact h1 xA
  exact h2 xB

-- --------------------------------- --
--      Union World - Level 4        --
-- --------------------------------- --
theorem union_subset_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x xAB
  -- Here's the rewrite as opposed to the have from level 3.
  rewrite [Set.mem_union x A B] at xAB
  cases' xAB with xA xB
  exact Or.inr xA
  exact Or.inl xB

-- --------------------------------- --
--      Union World - Level 5        --
-- --------------------------------- --
theorem union_comm (A B : Set U) : A ∪ B = B ∪ A := by
  apply Set.Subset.antisymm
  exact union_subset_swap A B
  exact union_subset_swap B A

-- --------------------------------- --
--      Union World - Level 6        --
-- --------------------------------- --
theorem union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply Set.Subset.antisymm

  intro x xABC
  have xABC : (x ∈ A ∨ x ∈ B) ∨ x ∈ C := xABC
  cases' xABC with xAB xC
  cases' xAB with xA xB
  exact Or.inl xA
  exact Or.inr (Or.inl xB)
  exact Or.inr (Or.inr xC)

  intro x xABC
  have xABC : x ∈ A ∨ (x ∈ B ∨ x ∈ C) := xABC
  cases' xABC with xA xBC
  exact Or.inl (Or.inl xA)
  cases' xBC with xB xC
  exact Or.inl (Or.inr xB)
  exact Or.inr xC

theorem union_assoc2 (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  apply Iff.intro

  intro xABC
  rewrite [Set.mem_union]
  rewrite [Set.mem_union]
  rewrite [Set.mem_union] at xABC
  rewrite [Set.mem_union] at xABC
  cases' xABC with xAB xC
  cases' xAB with xA xB
  exact Or.inl xA
  exact Or.inr (Or.inl xB)
  exact Or.inr (Or.inr xC)

  intro xABC
  rewrite [Set.mem_union]
  rewrite [Set.mem_union]
  rewrite [Set.mem_union] at xABC
  rewrite [Set.mem_union] at xABC
  cases' xABC with xA xBC
  exact Or.inl (Or.inl xA)
  cases' xBC with xB xC
  exact Or.inl (Or.inr xB)
  exact Or.inr xC

theorem union_assoc3 (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  apply Iff.intro

  -- And you can do it just like union_assoc2 without the rewrites.
  intro xABC
  cases' xABC with xAB xC
  cases' xAB with xA xB
  exact Or.inl xA
  exact Or.inr (Or.inl xB)
  exact Or.inr (Or.inr xC)

  intro xABC
  cases' xABC with xA xBC
  exact Or.inl (Or.inl xA)
  cases' xBC with xB xC
  exact Or.inl (Or.inr xB)
  exact Or.inr xC

-- --------------------------------- --
--   Combination World - Level 1     --
-- --------------------------------- --
theorem compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  apply Iff.intro

  intro xABCompl
  have xABCompl : ¬(x ∈ A ∨ x ∈ B) := xABCompl
  push_neg at xABCompl
  have xniA : x ∉ A := xABCompl.left
  have xniB : x ∉ B := xABCompl.right
  exact And.intro xniA xniB

  intro xABCompl
  have xABCompl : x ∉ A ∧ x ∉ B := xABCompl
  rewrite [mem_compl_iff]
  by_contra xinAB
  cases' xinAB with xA xB
  exact xABCompl.left xA
  exact xABCompl.right xB

-- A little shorter
theorem compl_union2 (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  apply Iff.intro

  intro xABCompl
  have xABCompl : ¬(x ∈ A ∨ x ∈ B) := xABCompl
  push_neg at xABCompl
  exact And.intro xABCompl.left xABCompl.right

  intro xABCompl
  rewrite [mem_compl_iff]
  by_contra xinAB
  cases' xinAB with xA xB
  exact xABCompl.left xA
  exact xABCompl.right xB

theorem compl_union3 (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  apply Iff.intro

  intro xABCompl
  have xABCompl : ¬(x ∈ A ∨ x ∈ B) := xABCompl
  push_neg at xABCompl
  exact xABCompl

  intro xABCompl
  by_contra xAB
  rewrite [mem_compl_iff] at xAB
  push_neg at xAB
  cases' xAB with xA xB
  exact xABCompl.left xA
  exact xABCompl.right xB

-- --------------------------------- --
--   Combination World - Level 2     --
-- --------------------------------- --
theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]
  rewrite [compl_union]
  -- Note: rw will not work in place of these in this context.
  -- TODO: Compare why these can't be rw compared to inter_assoc2 where the rewrites can be rws.
  rewrite [compl_compl A]
  rewrite [compl_compl B]
  rfl

-- --------------------------------- --
--   Combination World - Level 3     --
-- --------------------------------- --
theorem inter_distrib_left (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  apply Iff.intro

  intro xAnBuC
  have xA : x ∈ A := xAnBuC.left
  have xBuC : x ∈ B ∨ x ∈ C := xAnBuC.right -- You can do this without this line
  cases' xBuC with xB xC
  exact Or.inl (And.intro xA xB)
  exact Or.inr (And.intro xA xC)

  intro xAnBuAnC
  cases' xAnBuAnC with xAnB xAnC
  exact And.intro xAnB.left (Or.inl xAnB.right)
  exact And.intro xAnC.left (Or.inr xAnC.right)

theorem inter_distrib_left2 (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  apply Iff.intro

  -- Shorter variation.
  intro xAnBuC
  have xA : x ∈ A := xAnBuC.left
  cases' xAnBuC.right with xB xC
  exact Or.inl (And.intro xA xB)
  exact Or.inr (And.intro xA xC)

  intro xAnBuAnC
  cases' xAnBuAnC with xAnB xAnC
  exact And.intro xAnB.left (Or.inl xAnB.right)
  exact And.intro xAnC.left (Or.inr xAnC.right)

-- --------------------------------- --
--   Combination World - Level 4     --
-- --------------------------------- --
theorem union_distrib_left (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro

  intro xABC
  cases' xABC with xA xBC
  exact And.intro (Or.inl xA) (Or.inl xA)
  exact And.intro (Or.inr xBC.left) (Or.inr xBC.right)

  intro xABC
  cases' xABC.left with xA xB
  exact Or.inl xA
  cases' xABC.right with xA xC
  exact Or.inl xA
  exact Or.inr (And.intro xB xC)

-- This one uses inter_distrib, but I like it less.
theorem union_distrib_left2 (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro

  intro xABC
  cases' xABC with xA xBC
  exact And.intro (Or.inl xA) (Or.inl xA)
  exact And.intro (Or.inr xBC.left) (Or.inr xBC.right)

  intro xABC
  rewrite [inter_distrib_left (A ∪ B) A C] at xABC
  cases' xABC with xAuBnA xAuBnC
  exact Or.inl xAuBnA.right
  have xC : x ∈ C := xAuBnC.right
  cases' xAuBnC.left with xA xB
  exact Or.inl xA
  exact Or.inr (And.intro xB xC)

-- --------------------------------- --
--   Combination World - Level 5     --
-- --------------------------------- --
example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x xA

  have xAC : x ∈ A ∪ C := Or.inl xA
  have xBC : x ∈ B ∪ C := h1 xAC
  cases' xBC with xB xC
  exact xB
  have xBnC : x ∈ B ∩ C := h2 (And.intro xA xC)
  exact xBnC.left

-- ------------------------------------- --
--  Family Intersection World - Level 1  --
-- ------------------------------------- --
-- TODO: Come back and study this.
example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  -- We need an element to do element based arguments.
  -- Let this be the element.
  intro x

  -- We start with this goal
  --   ⋂₀ F ⊆ A
  -- and we want to transform it into the following
  --   (∀ t ∈ F, x ∈ t) → x ∈ A
  -- which states that if x is in every set in F, then x ∈ A.
  rewrite [Set.mem_sInter]

  -- Suppose ∀ t ∈ F, x ∈ t ...
  -- This is shorthand for ∀ t, t ∈ F → x ∈ t
  --
  -- !!!! This is the point we're supposing that x ∈ ⋂₀ F ...
  intro sup

  -- Since A ∈ F, by the supposition, it must be the case that x ∈ A.
  apply sup at h1

  -- x ∈ A is exactly what want to show.
  exact h1

-- ------------------------------------- --
--  Family Intersection World - Level 2  --
-- ------------------------------------- --
example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x

  rewrite [Set.mem_sInter]
  rewrite [Set.mem_sInter]

  intro sup

  -- Before this command, the goal is
  --   ∀ t ∈ F, x ∈ t
  -- and after intro will become
  --   t ∈ F → x ∈ t
  intro t

  intro tF
  apply h1 at tF
  apply sup at tF
  exact tF


-- ------------------------------------- --
--  Family Intersection World - Level 3  --
-- ------------------------------------- --
-- stucky's solution
example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  apply Set.Subset.antisymm
  intro x xAB
  rw [Set.mem_sInter]
  intro t
  --rw[mem_pair]
  intro tAB
  cases' tAB with tA tB
  rw[tA]
  apply xAB.left
  rw[tB]
  exact xAB.right

  intro x xPAIR
  apply And.intro

  apply xPAIR
  --rw[mem_pair]
  have h : A=A := by rfl
  exact Or.inl h

  apply xPAIR
  --rw[mem_pair]
  have h : B=B := by rfl
  exact Or.inr h
