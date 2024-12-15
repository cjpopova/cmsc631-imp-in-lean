import Mathlib.Data.Real.Basic
import Mathlib.Data.Finsupp.AList
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith.Frontend

def total_map (A : Type) := String -> A

def t_empty {A: Type} (v: A) : total_map A :=
(fun _ => v)

def t_update {A: Type}(m: total_map A)(x: String)(v :A) :=
  fun y => if (x == y) then v else (m y)

notation:max "_ !->" v => (t_empty v)
notation:max x "!->" v "≀" m => (t_update m x v) -- unicode symbol: wr

def ex_map := "y" !-> 6 ≀ ("x" !-> 3 ≀ (_ !-> 0))

#eval (t_update ex_map "x" 4) "x"

def state := total_map Nat
def empty_st := (_ !-> 0)

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

@[simp]
def aeval (st: state)(a : aexp) : Nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus  a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult  a1 a2 => (aeval st a1) * (aeval st a2)

open bexp
@[simp]
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
-- notation: max (priority := high) "True" => BTrue -- (in custom com at level 0)
-- notation: max "'false'" => false (at level 1)
notation: max (priority := high) "False" => BFalse -- (in custom com at level 0)
--notation: max (priority := high) x "<=" y => BLe x y -- (in custom com at level 70, no associativity)
notation: max (priority := high) x ">" y => BGt x y -- (in custom com at level 70, no associativity)
notation: max (priority := high) x "==" y => BEq x y --(in custom com at level 70, no associativity)
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
--def example_bexp : bexp := <{ BTrue && ~(X <= 4) }>
end

-- Open the scope for `com_scope`
-- open_locale com_scope

-- -- Example arithmetic and boolean expressions
-- def example_aexp : aexp := <{ 3 + (X * 2) }>
-- def example_bexp : bexp := <{ true && ~(X <= 4) }>


open com
notation: max "skip" => CSkip
notation: max x "::=" y => (CAsgn x y)
notation: max x ";;" y => (CSeq x y)
notation: max "if" x "then" y "else" z "endL" => (CIf x y z)
notation: max "while" x "doW" y "endL" => (CWhile x y)


open with_state
#eval (ANum 1)

open with_state

def ex_1 : com := ("Z" ::= (AId "X"))

def ex_2 : com :=
("Z" ::= (AId "X")) ;;
("Y" ::= (ANum 1)) ;;
while (BNeq (AId "Z") (ANum 0)) doW
  ("Y" ::= (AId "Y")) ;;
  ("Y" ::= (ANum 1))
endL

def fact_in_lean : com :=
("Z" ::= "X") ;;
("Y" ::= 1) ;;
while (BNeq (AId "Z") (ANum 0)) doW
  ("Y" ::= "Y" * "Z") ;;
  ("Y" ::= "Z" - 1)
endL


-- Y := (ANum 1);
-- while (Z != 0) doW (Y := (Y * Z)) endL


-- notation:max "_ !->" v => (t_empty v)
-- notation:max x "!->" v ";" m => (t_update m x v)

-- def ex_map := "y" !-> 6; ("x" !-> 3; (_ !-> 0))


------------ BEGIN HOARE --------------
def Assertion := state -> Prop

open aexp

namespace ExampleAssertions
  def assertion1 : Assertion := fun (st) => (st "X") < (st "Y")
  def assertion2 : Assertion := fun (st) => (st "X") = 3 \/ (st "X") < (st "Y")
  --def assertion3 : Assertion := fun st => st "Z" * st "Z" < (st "X") /\ ~ (((S + (st "Z")) * (S (st "Z"))) <= st "X")

end ExampleAssertions

def assert_implies (P Q : Assertion) : Prop := forall st, P st -> Q st

notation:max P "->>" Q   => (assert_implies P Q)
--notation:max P "<<->>" Q => (P ->> Q /\ Q ->> P)


inductive ceval : com -> state -> state -> Prop where
  | E_Skip : forall st,
      ceval skip st st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      ceval (CAsgn x a1) st (x !-> n ≀ st)
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st'  ->
      ceval c2 st' st'' ->
      ceval (c1 ;; c2) st st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      ceval c1 st st' ->
      ceval (if b then c1 else c2 endL) st st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      ceval c2 st st' ->
      ceval (if b then c1 else c2 endL) st  st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      ceval (while b doW c endL) st st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      ceval c st st' ->
      ceval (while b doW c endL) st' st'' ->
      ceval (while b doW c endL) st st''

notation:max st "=[" c "]=>" st2 => (ceval c st st2)

def valid_hoare_triple (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall (st : state) (st' : state),
  (st =[ c ]=> st') -> P st -> (Q st')

-- This notation doesn't work.
-- notation:max "{{" P "}}" c "{{" Q "}}" => (valid_hoare_triple P c Q)

-- Example hoare proof
theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  (valid_hoare_triple P c Q) --({{P}} c {{Q}})
   := by
  intros P Q c H
  unfold valid_hoare_triple
  intros st st' H0 H1
  apply H st'

theorem hoare_skip : forall P, (valid_hoare_triple P CSkip P) := by
  intros P st st' H HP
  cases H
  . apply HP

theorem hoare_seq : forall P Q R c1 c2,
    (valid_hoare_triple Q c2 R) ->
    (valid_hoare_triple P c1 Q) ->
    (valid_hoare_triple P (c1 ;; c2) R) := by
  unfold valid_hoare_triple
  intros P Q R c1 c2 H1 H2 st st' H12 Pre
  cases H12
  . aesop

def assertion_sub (X : String) (a : aexp) (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ≀ st)

notation P "[" X "|->" a "]" => (assertion_sub X a P)

theorem hoare_asgn : forall Q X a,
  valid_hoare_triple (Q [X |-> a]) (X ::= a) Q -- {{Q [X |-> a]}} X := a {{Q}}.
  := by
  unfold valid_hoare_triple
  intros Q X a st st' HE HQ
  cases HE
  . rename_i n Ha
    unfold assertion_sub at HQ
    rw [<- Ha]
    apply HQ

lemma assertion_sub_example :
  valid_hoare_triple
    (assertion_sub X (X + 1) (fun (st) => ((st X) < 5))) -- (X < 5) [X |-> X + 1]
    (X ::= X + 1)
    (fun (st) => ((st X) < 5)) -- X < 5
   := by
  apply hoare_asgn


theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
    valid_hoare_triple P' c Q -> -- {{P'}} c {{Q}} ->
    (P ->> P') ->
    valid_hoare_triple P c Q -- {{P}} c {{Q}}.
    := by
  unfold valid_hoare_triple
  unfold assert_implies
  aesop


theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  valid_hoare_triple P c Q' -> -- {{P}} c {{Q'}} ->
  (Q' ->> Q) ->
  valid_hoare_triple P c Q -- {{P}} c {{Q}}.
  := by
  unfold valid_hoare_triple
  unfold assert_implies
  intros P Q Q' c Hhoare Himp st st' Heval Hpre
  aesop

theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  valid_hoare_triple P' c Q' -> -- {{P'}} c {{Q'}} ->
  (P ->> P') ->
  (Q' ->> Q) ->
  valid_hoare_triple P c Q -- {{P}} c {{Q}}.
  := by
  intros P P' Q Q' c Htriple Hpre Hpost
  apply hoare_consequence_pre P P' Q -- with (P' := P')
  apply hoare_consequence_post P' Q Q'
  apply Htriple
  apply Hpost
  apply Hpre

lemma hoare_asgn_example3 : forall (a:aexp) (n:Nat),
  valid_hoare_triple (fun (st) => a = (ANum n)) --{{a = n}}
    ((X ::= a);; skip)
  (fun (st) => st X = n) -- {{X = n}}.
  := by
  intros a n
  apply hoare_seq
  . apply hoare_skip
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . unfold assertion_sub
      unfold t_update
      intros st H
      simp
      aesop

def bassertion (b:bexp) : Assertion :=
  fun st => (beval st b = true)


@[aesop unsafe 50% apply]
lemma bexp_eval_false : forall (b:bexp) st,
  beval st b = false -> ¬ ((bassertion b) st) := by
    intros b st H
    unfold bassertion
    rw [H]
    aesop

theorem hoare_if : forall P Q b c1 c2,
  valid_hoare_triple (fun st => P st /\ (bassertion b st)) c1 Q ->
  valid_hoare_triple (fun st => P st /\ ¬ (bassertion b st)) c2 Q ->
  valid_hoare_triple P (if b then c1 else c2 endL) Q
  := by
  intros P q b c1 c2 HTrue HFalse st st' HE HP
  cases HE
  . aesop
  . apply HFalse
    . aesop
    . constructor
      . apply HP
      . apply bexp_eval_false; assumption

-- CJP: I'm sure this exists in the standard library, but I can't find it.
lemma implies_false : ¬ A = B -> (A = B) = false := by aesop

lemma if_example :
  valid_hoare_triple
    (fun st => True) -- {{True}}
    (if ("X" == 0)
      then ("Y" ::= 2)
      else ("Y" ::= "X" + 1)
    endL)
    (fun st => (st "X") <= (st "Y")) -- {{X <= Y}} -- CJP: I don't why this notation works
  := by
  unfold valid_hoare_triple
  apply hoare_if
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . unfold assert_implies
      unfold assertion_sub
      unfold t_update
      unfold bassertion
      simp
      intros st H
      by_cases ("Y"="X") <;> try aesop
  . apply hoare_consequence_pre
    . apply hoare_asgn
    . unfold assert_implies
      unfold assertion_sub
      unfold t_update
      unfold bassertion
      simp

@[aesop 50 unsafe 60%]
theorem hoare_while : forall (P:Assertion) (b:bexp) c,
  valid_hoare_triple (fun st => P st /\ bassertion b st) c P ->
  valid_hoare_triple P (while b doW c endL) (fun st => P st /\ ¬ (bassertion b st))
  := by
  intros P b c Hhoare st st' Heval HP
  generalize Horig : (while b doW c endL) = original_command
  rw [Horig] at Heval -- because https://leanprover-community.github.io/archive/stream/270676-lean4/topic/induction.20with.20fixed.20index.html
  induction Heval <;> cases Horig <;> aesop
  · unfold bassertion at a_1
    rw [a] at a_1
    contradiction
  · unfold valid_hoare_triple at Hhoare
    apply Hhoare at a_1
    simp at a_1
    apply a_1 at HP
    unfold bassertion at HP
    apply HP at a
    apply a_ih_1 at a
    cases a
    rename_i l r
    apply l
  · unfold valid_hoare_triple at Hhoare
    apply Hhoare at a_1
    simp at a_1
    apply a_1 at HP
    unfold bassertion at HP
    apply HP at a
    contradiction


lemma while_example : -- this example comes from Hoare.v
  valid_hoare_triple
    (fun st => (st "X") <= 3)  -- {{X <= 3}}
    while (BLe "X" 2) doW
      (X ::= "X" + 1)
    endL
    (bassertion ("X" == 3)) -- {{X = 3}}.
:= by
  unfold valid_hoare_triple
  apply hoare_consequence_post
  . apply hoare_while
    apply hoare_consequence_pre
    . apply hoare_asgn
    . unfold assert_implies
      unfold  assertion_sub
      unfold t_update
      unfold bassertion
      simp
      intros st
      by_cases (X="X") <;> try aesop
  . unfold bassertion
    simp
    intros st
    by_cases (X="X") <;> try aesop
    . linarith
    . linarith


----------- END HOARE ------------------------

/-theorem while_ex1 : ∀ st,
  st =[while ((AId "X") <= (ANum 4)) doW
    (("Y" ::= "Y" + 2); ("X" ::= "X" + 1)) endL]=> := -/

theorem ceval_example1:
    empty_st =[
       ("X" ::= (ANum 2));;
      if (BLe "X" 1)
        then "Y" ::= 3
        else "Z" ::= 4
      endL
   ]=> ("Z" !-> 4 ≀ ("X" !-> 2 ≀ empty_st)) := by
  apply ceval.E_Seq (CAsgn "X" (ANum 2)) (CIf (BLe "X" 1) ("Y" ::= 3) ("Z" ::= 4)) empty_st ("X" !-> 2 ≀ empty_st) ("Z" !-> 4 ≀ ("X" !-> 2 ≀ empty_st))
  · apply ceval.E_Asgn
    rfl
  · apply ceval.E_IfFalse
    · rfl
    · apply ceval.E_Asgn
      rfl

theorem ceval_deterministic: ∀ c st st1 st2,
  (st =[ c ]=> st1)  ->
  (st =[ c ]=> st2) ->
  st1 = st2 := by
  intros c st st1 st2 E1 E2
  revert st2
  induction E1 <;> intros st2 E2 <;> cases E2 <;> try aesop
  . rename_i c1 c2 stt stt' stt'' at1 at2 a_iht1 a_iht2 sttt' as1 as2;
    have test := a_iht1 sttt' as1; aesop
  . have newih := a_ih st'_1 a_4; aesop

end with_state
