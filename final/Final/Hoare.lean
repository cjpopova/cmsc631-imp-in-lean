import Mathlib.Data.Real.Basic
import Final.Basic

def X : String := "X"
def Y : String := "Y"

def Assertion := state -> Prop

open aexp

namespace ExampleAssertions
  def assertion1 : Assertion := fun st => st (aexp.AId "X") <= st Y.

end ExampleAssertions

/-
Module ExAssertions.
Definition assertion1 : Assertion := fun st => st X <= st Y.
Definition assertion2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assertion3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assertion4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* FILL IN HERE *)
End ExAssertions.
-/
