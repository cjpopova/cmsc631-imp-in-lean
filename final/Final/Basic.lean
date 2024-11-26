import Mathlib.Data.Real.Basic

inductive aexp where
  | ANum (n : Nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)

open aexp -- open namespace
#check (APlus (ANum 3))

inductive bexp where
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)

open bexp
#check BTrue
#check (BEq (ANum 3) (ANum 3))

------------- Evaluation as functions ----------------------

def aeval (a : aexp) : Nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)

def beval (b : bexp) : Bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | bexp.BEq a1 a2   => (aeval a1) = (aeval a2)
  | BNeq a1 a2  => ¬ ((aeval a1) = (aeval a2))
  | BLe a1 a2   => (aeval a1) <= (aeval a2)
  | BGt a1 a2   => ¬ ((aeval a1) <= (aeval a2))
  | BNot b1     => ¬ (beval b1)
  | BAnd b1 b2  =>  (beval b1) ∧ (beval b2)

---------------- Evaluation as a Relation ----------------------


