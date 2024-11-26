import Mathlib.Data.Real.Basic

/-
# Reference
The order of operations is as follows: unary negation ¬ binds most strongly, then ∧, then ∨, then →, and finally ↔

Or.elim ............. destruct ∨ in the context
Or.inl, Or.inr ...... prove (intro) one side of ∨ in the goal
And.left, And.right . destruct (eliminate) ∧ in the context
And.intro ........... prove both sides of ∧ in the goal
Iff.intro ........... destruct ↔ in the goal

h := a ∨ b
cases h with
| ha => ...
| hb => ...

h := a ∧ b
cases h with
| intro ha hb => ...

h := ∃ x, p x
cases h with
| intro x px =>

rewrite:
If h : a = b then rw h turns all a s in the goal to b s.
If you only want to turn one of the a s into a b, use nth_rewrite.
For example nth_rewrite 2 h will change only the third a into b
use `rw [← h]` (slash l) to rewrite backwards

-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

/- Example from basic tactics
 https://lean-lang.org/theorem_proving_in_lean4/tactics.html -/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro -- we need to prove IFF both forwards and backwards (equivalent to Coq's `split`)
  . -- ⊢ p ∧ (q ∨ r) → p ∧ q ∨ p ∧ r
    intro h -- everything before → becomes h
    apply Or.elim (And.right h) -- 2 cases from (q ∨ r)
    . intro hq
      apply Or.inl -- we will prove LHS of the goal
      apply And.intro -- we will prove both sides of p ∧ q
      . exact And.left h -- get the left side of h
      . exact hq
    . intro hr -- ⊢ p ∧ q ∨ p ∧ r (also written as (p ∧ q) ∨ (p ∧ r))
      apply Or.inr -- we will prove RHS
      apply And.intro
      . exact And.left h
      . exact hr
  . -- ⊢ p ∧ q ∨ p ∧ r → p ∧ (q ∨ r)
    intro h
    apply Or.elim h -- start by destructing the hypothesis into hpq | hpr
    . intro hpq
      apply And.intro -- similar to Coq's `split`, we need to prove both sides
      . exact And.left hpq
      . apply Or.inl -- we will prove LHS
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

-- i will now rewrite a template of this proof using `case` instead or `Or.elim`
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro -- we need to prove IFF both forwards and backwards (equivalent to Coq's `split`)
  . -- ⊢ p ∧ (q ∨ r) → p ∧ q ∨ p ∧ r
    intro h
    cases (And.right h) with
    | inl hp => admit
    | inr hqr => admit
  . admit

-- Ah, here's the book's official rewrite:
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      . apply Or.inl; constructor <;> assumption
      . apply Or.inr; constructor <;> assumption
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | intro hp hq => constructor; exact hp; apply Or.inl; exact hq
    | inr hpr =>
      cases hpr with
      | intro hp hr => constructor; exact hp; apply Or.inr; exact hr


example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x
