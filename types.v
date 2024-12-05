Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.


(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Module Exp.
Inductive value : Type :=
  | VUnit : value
  | VInt : Z -> value
  | VRefMut : Z -> value
  | VRefImmMut : Z -> value.

Inductive expression : Type :=
  | Evalue: value -> expression                   
  | EVar : Z -> expression                            
  | EAssign : Z -> expression -> expression        
  | EMutBorrow : Z -> expression             
  | EImmBorrow : Z -> expression             
  | EDeref : expression -> expression                
  | ELet : Z -> expression -> expression -> expression   
  | ESequence : expression -> expression -> expression.          


Inductive ownership : Type :=
| Own : value -> ownership 
| BorrowMut : nat -> ownership               
| BorrowImm : list nat -> ownership. 

Definition memory_state := nat -> option ownership.

Definition lifetime_state := nat -> nat.

Inductive borrow_state : Type :=
| MutBorrowed : nat -> borrow_state
| ImmBorrowed : list nat -> borrow_state.

Definition update_memory (h : memory_state) (loc : nat) (v : option ownership) : memory_state :=
  fun l => if l =? loc then v else h l.


Fixpoint eval (m : memory_state) (e : expression) : option (memory_state * value) :=
  match e with
  | EVal v => Some (h, v)
  | EAdd e1 e2 =>
      match eval h e1, eval h e2 with
      | Some (h1, VInt v1), Some (h2, VInt v2) => Some (h2, VInt (v1 + v2))
      | _, _ => None
      end
  | ESub e1 e2 =>
      match eval h e1, eval h e2 with
      | Some (h1, VInt v1), Some (h2, VInt v2) => Some (h2, VInt (v1 - v2))
      | _, _ => None
      end
  | EMul e1 e2 =>
      match eval h e1, eval h e2 with
      | Some (h1, VInt v1), Some (h2, VInt v2) => Some (h2, VInt (v1 * v2))
      | _, _ => None
      end
  | EMutBorrow x =>
      match h x with
      | Some (Own v) => Some (update_heap h x (Some (BorrowMut x)), VRefMut x)
      | _ => None
      end
  | EImmBorrow x =>
      match h x with
      | Some (Own v) => Some (update_heap h x (Some (BorrowImm [x])), VRefImm x)
      | _ => None
      end
  | EDeref e1 =>
      match eval h e1 with
      | Some (h1, VRefMut x) => match h x with Some (Own v) => Some (h1, v) | _ => None end
      | Some (h1, VRefImm x) => match h x with Some (Own v) => Some (h1, v) | _ => None end
      | _ => None
      end
  | _ => None 
  end.


Inductive borrow_valid : memory_state -> nat -> borrow_state -> Prop :=
  | BorrowMutValid : forall h x,
      h x = Some (BorrowMut x) ->
      borrow_valid h x (MutBorrowed x)
  | BorrowImmValid : forall h x l,
      h x = Some (BorrowImm l) ->
      Forall (fun r => h r = Some (BorrowImm l)) l ->
      borrow_valid h x (ImmBorrowed l).


Inductive has_type : lifetime_state -> memory_state -> expression -> ref_type -> Prop :=
| TVal : forall l h v,
    has_type l h (EVal v) (RefImm 0) (* Values are immutable *)
| TAdd : forall l h e1 e2,
    has_type l h e1 (RefImm 0) -> (* Operands must be integers *)
    has_type l h e2 (RefImm 0) ->
    has_type l h (EAdd e1 e2) (RefImm 0)
| TMutBorrow : forall l h x t,
    has_type l h (EVar x) (RefMut t) ->
    has_type l h (EMutBorrow x) (RefMut t)
| TImmBorrow : forall l h x t,
    has_type l h (EVar x) (RefImm t) ->
    has_type l h (EImmBorrow x) (RefImm t).


End Exp.