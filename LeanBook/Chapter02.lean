-- Theorem Proving in Lean 4
-- Notes from Chapter 2
-- https://leanprover.github.io/theorem_proving_in_lean4/dependent_type_theory.html
-- May 8, 2024

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
