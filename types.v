Require Import Coq.ZArith.ZArith.



(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Module AExp.
Inductive aexp : Type :=
  | ANum (z : Z)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive uexp : Type :=
  | Unit.


Fixpoint aeval (a : aexp) : Z :=
  match a with
  | ANum z => z
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  | ADiv a1 a2 => (aeval a1) / (aeval a2)
  end.

End AExp.