import Mathlib.Data.Real.Basic
import Mathlib.Data.Finsupp.AList

def total_map (A : Type) := String -> A

def t_empty {A: Type} (v: A) : total_map A :=
(fun _ => v)

def t_update {A: Type}(m: total_map A)(x: String)(v :A) :=
  fun y => if (x == y) then v else (m y)

notation:max "_ !->" v => (t_empty v)
notation:max x "!->" v ";" m => (t_update m x v)

def ex_map := "y" !-> 6; ("x" !-> 3; (_ !-> 0))

#eval (t_update ex_map "x" 4) "x"

def state := total_map Nat

namespace no_state
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
      rw [<- H]; rw [beval]; apply bevalR.E_BEq;
      . have aiar := aeval_iff_aevalR a1 (aeval a1); apply aiar.mpr; rfl;
      . have aiar := aeval_iff_aevalR a2 (aeval a2); apply aiar.mpr; rfl;
    case mpr.BNeq a1 a2 =>
      rw [<- H]; rw [beval]; apply bevalR.E_BNeq;
      . have aiar := aeval_iff_aevalR a1 (aeval a1); apply aiar.mpr; rfl;
      . have aiar := aeval_iff_aevalR a2 (aeval a2); apply aiar.mpr; rfl;
    case mpr.BLe a1 a2 =>
      rw [<- H]; rw [beval]; apply bevalR.E_BLe;
      . have aiar := aeval_iff_aevalR a1 (aeval a1); apply aiar.mpr; rfl;
      . have aiar := aeval_iff_aevalR a2 (aeval a2); apply aiar.mpr; rfl;
    case mpr.BGt a1 a2 =>
      rw [<- H]; rw [beval]; apply bevalR.E_BGt;
      . have aiar := aeval_iff_aevalR a1 (aeval a1); apply aiar.mpr; rfl;
      . have aiar := aeval_iff_aevalR a2 (aeval a2); apply aiar.mpr; rfl;
    case mpr.BNot b1 H1 =>
      rw [<- H]; rw [beval]; apply bevalR.E_BNot; apply H1; rfl
    case mpr.BAnd b1 b2 H1 H2 =>
      rw [<- H]; rw [beval]; simp; apply bevalR.E_BAnd;
      . apply H1; rfl
      . apply H2; rfl




end no_state

namespace with_state

inductive aexp where
  | ANum (n : Nat)
  | AId (x: String)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)

inductive bexp where
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)

open aexp

def aeval (st: state)(a : aexp) : Nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus  a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult  a1 a2 => (aeval st a1) * (aeval st a2)

open bexp
def beval (st: state)(b : bexp) : Bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | bexp.BEq a1 a2   => (aeval st a1) = (aeval st a2)
  | BNeq a1 a2  => ¬ ((aeval st a1) = (aeval st a2))
  | BLe a1 a2   => (aeval st a1) <= (aeval st a2)
  | BGt a1 a2   => ¬ ((aeval st a1) <= (aeval st a2))
  | BNot b1     => ¬ (beval st b1)
  | BAnd b1 b2  =>  (beval st b1) ∧ (beval st b2)

#eval aeval (_ !-> 0) (ANum  5)

theorem test2: aeval (_ !-> 0) (APlus (ANum 2) (ANum 2)) = 4 :=
by rfl

open with_state
inductive com : Type where
  | CSkip
  | CAsgn (x : String) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)

namespace Test

-- @[coercion]
-- def AId : String → aexp := aexp.AId

instance : OfNat aexp (n : Nat) where
  ofNat := aexp.ANum n

instance : Coe String aexp where
  coe := aexp.AId

-- @[coercion]
-- def ANum : Nat → aexp := aexp.ANum

notation: max "<{" e "}>" => e

notation: max (priority := 2000) "(" x ")" => x

notation: max (priority := high) x "+" y => APlus x y -- (in custom com at level 50, left associativity)
notation: max (priority := high) x "-" y => AMinus x y  -- (in custom com at level 50, left associativity)
notation: max (priority := high) x "*" y => AMult x y -- (in custom com at level 40, left associativity)
-- notation: max "true'" => true -- (at level 1)
notation: max (priority := high) "True" => BTrue -- (in custom com at level 0)
-- notation: max "'false'" => false (at level 1)
notation: max (priority := high) "False" => BFalse -- (in custom com at level 0)
notation: max (priority := high) x "<=" y => BLe x y -- (in custom com at level 70, no associativity)
notation: max (priority := high) x ">" y => BGt x y -- (in custom com at level 70, no associativity)
notation: max (priority := high) x "=" y => BEq x y --(in custom com at level 70, no associativity)
notation: max (priority := high) x "<>" y => BNeq x y -- (in custom com at level 70, no associativity)
notation: max (priority := high) x "&&" y => BAnd x y -- (in custom com at level 80, left associativity)
notation: max (priority := high) "~" b => BNot b  -- (in custom com at level 75, right associativity)
def W : String := "W"
def X : String := "X"
def Y : String := "Y"
def Z : String := "Z"

end Test

-- Open the custom scope for `com_scope`
-- open_locale com_scope

-- Example arithmetic and boolean expressions
section
open Test
def example_aexp111 : aexp := <{(X * 2)}>
def example_aexp : aexp := <{3 + (X * 2) }>
def example_bexp : bexp := <{ True && ~(X <= 4) }>
end

-- Open the scope for `com_scope`
-- open_locale com_scope

-- -- Example arithmetic and boolean expressions
-- def example_aexp : aexp := <{ 3 + (X * 2) }>
-- def example_bexp : bexp := <{ true && ~(X <= 4) }>


open com
notation: max "skip" => CSkip
notation: max x "::=" y => (CAsgn x y)
notation: max x ";" y => (CSeq x y)
notation: max "if" x "then" y "else" z "endL" => (CIf x y z)
notation: max "while" x "doW" y "endL" => (CWhile x y)


open with_state
#eval (ANum 1)

open with_state
def fact_in_lean : com :=
("Z" ::= (AId "X")) ;
("Y" ::= (ANum 1)) ;
while (BNeq (AId "Z") (ANum 0)) doW
  ("Y" ::= (AId "Y")) ;
  ("Y" ::= (ANum 1)) ;





-- Y := (ANum 1);
-- while (Z != 0) doW (Y := (Y * Z)) endL


-- notation:max "_ !->" v => (t_empty v)
-- notation:max x "!->" v ";" m => (t_update m x v)

-- def ex_map := "y" !-> 6; ("x" !-> 3; (_ !-> 0))


end with_state
