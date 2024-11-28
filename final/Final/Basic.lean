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


#eval aeval (ANum 5)

theorem test2: aeval (APlus (ANum 2) (ANum 2)) = 4 :=
by rfl


---------------- Evaluation as a Relation ----------------------

inductive aevalR : aexp -> Nat -> Prop where
  | E_ANum (n : Nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : Nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : Nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : Nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2)

inductive bevalR: bexp -> Bool -> Prop where
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : ∀ (a1 a2 : aexp) (n1 n2 : Nat),
      (aevalR a1 n1) ->
      (aevalR a2 n2) ->
      bevalR (BEq a1 a2) (n1 = n2)
  | E_BNeq : ∀ (a1 a2 : aexp) (n1 n2 : Nat),
    (aevalR a1 n1) ->
    (aevalR a2 n2) ->
    bevalR (BNeq a1 a2) (¬ (n1 = n2))
  | E_BLe : ∀ (a1 a2 : aexp) (n1 n2 : Nat),
    (aevalR a1 n1) ->
    (aevalR a2 n2) ->
    bevalR (BLe a1 a2) (n1 <= n2)
  | E_BGt : ∀ (a1 a2 : aexp) (n1 n2 : Nat),
    (aevalR a1 n1) ->
    (aevalR a2 n2) ->
    bevalR (BGt a1 a2) (¬ (n1 <= n2))
  | E_BNot : ∀ (b : bexp) (b' : Bool),
    (bevalR b b') ->
    bevalR (BNot b) (¬b')
  | E_BAnd : ∀ (b1 b2 : bexp) (b1' b2' : Bool),
    (bevalR b1 b1') ->
    (bevalR b2 b2') ->
    bevalR (BAnd b1 b2) (and b1' b2')

-- Add notation
infixl:65   " ==> " => aevalR  -- left-associative
infixl:65   " ==>b " => bevalR  -- left-associative

---------  Equivalence of evaluation as functions vs relations ------------

theorem aeval_iff_aevalR : ∀ a n, (a ==> n) <-> aeval a = n := by
  intros a n
  constructor
  · intros H
    induction H <;> try
      {rw [aeval]; rename_i H1_ih H2_ih; rw [H1_ih]; rw [H2_ih]}
    rfl
  . revert n; induction a <;> intros n H;
    case mpr.ANum n =>
      rw [aeval.eq_def] at H; simp at H; rewrite [H]; constructor
    case mpr.APlus a1_ih a2_ih =>
      rw [<- H]; rw [aeval]; apply aevalR.E_APlus;
      apply a1_ih; rfl; apply a2_ih; rfl
    case mpr.AMinus a1_ih a2_ih =>
      rw [<- H]; rw [aeval]; apply aevalR.E_AMinus;
      apply a1_ih; rfl; apply a2_ih; rfl
    case mpr.AMult a1_ih a2_ih =>
      rw [<- H]; rw [aeval]; apply aevalR.E_AMult;
      apply a1_ih; rfl; apply a2_ih; rfl

theorem beval_iff_bevalR : ∀ b bv, b ==>b bv <-> beval b = bv := by
  intros b bv
  constructor
  . intros H
    induction H
      -- 2 IH on arithmetic operands (le, gt, etc)
      <;> try { rw [beval]; rename_i H1_ih H2_ih; rw [aeval_iff_aevalR] at H1_ih; rw [aeval_iff_aevalR] at H2_ih; rw [H1_ih]; rw [H2_ih] }
      -- base cases
      <;> try { rfl }
    -- 1 IH on boolean
    rw [beval]; rename_i H1_ih; rw [H1_ih]
    -- 2 IH on boolean
    rw [beval]; rename_i H1_ih H2_ih; rw [H1_ih]; rw [H2_ih]; simp
  . revert bv; induction b <;> intros b H
      <;> try { rw [beval.eq_def] at H; simp at H; rewrite [H]; constructor }
    case mpr.BEq a1 a2 =>
      rw [<- H]; rw [beval]; apply bevalR.E_BEq; apply aeval_iff_aevalR
