Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.


Module Exp.

Inductive mem_loc : Type :=
| MemLoc : nat -> mem_loc.

Definition mem_loc_to_nat (loc : mem_loc) : nat :=
match loc with
  | MemLoc n => n
end.


Inductive ref_type : Type :=
| RefMut : mem_loc -> ref_type  
| RefImm : mem_loc -> ref_type.

Definition ref_to_mem_loc (ref : ref_type) : mem_loc :=
match ref with
| RefMut loc => loc
| RefImm loc => loc
end.

Inductive value : Type :=
| VUnit : value
| VInt : Z -> value
| VRefMut : ref_type -> value
| VRefImmMut : ref_type -> value.

Inductive var : Type := 
| Var : nat -> var. 

Definition var_to_nat (v : var) : nat :=
match v with
  | Var n => n
end.

Inductive expression : Type :=
| EValue: value -> expression                   
| EVar : var -> expression                            
| EAssign : mem_loc -> expression -> expression        
| EMutBorrow : mem_loc -> expression             
| EImmBorrow : mem_loc -> expression             
| EDeref : expression -> expression                
| ELet : var -> expression -> expression -> expression
| EMut : var -> expression -> expression
| ESequence : expression -> expression -> expression.          


Inductive ownership : Type :=
| Own : value -> ownership 
| BorrowMut : mem_loc -> ownership               
| BorrowImm : list mem_loc -> ownership
| OwnMut : value -> ownership.

Definition memory_state := mem_loc -> option ownership.

Definition lifetime_state := nat -> nat.

Inductive borrow_state : Type :=
| MutBorrowed : mem_loc -> borrow_state
| ImmBorrowed : list mem_loc -> borrow_state.

Definition update_memory (m : memory_state) (loc : mem_loc) (v : option ownership) : memory_state :=
fun l => 
  if Nat.eqb (mem_loc_to_nat l) (mem_loc_to_nat loc) then v 
  else m l.


Fixpoint eval (m : memory_state) (e : expression) : option (memory_state * value) :=
match e with
  | EValue v => Some (m, v)
  | EVar x =>
      match m (MemLoc (var_to_nat x)) with
        | Some (Own v) => Some (m, v)
        | Some (OwnMut v) => Some (m, v)
        | _ => None
      end
  | EAssign loc e' =>
    match eval m e' with
      | Some (m', v) =>
          match m loc with
          | Some (OwnMut _) =>
              Some (update_memory m' loc (Some (OwnMut v)), v)
          | _ => None
          end
      | _ => None
    end
  | EMut loc e' =>
    match m (MemLoc (var_to_nat loc)) with
    | Some _ => None (* Fail if loc is already in use *)
    | None =>
        match eval m e' with
        | Some (m', v) =>
            match v with
            | VInt _ => Some (update_memory m' (MemLoc (var_to_nat loc)) (Some (OwnMut v)), VUnit)
            | _ => None (* Invalid value for mutable binding *)
            end
        | _ => None
        end
    end
  | EMutBorrow loc =>
      match m loc with
      | Some (Own v) =>
          Some (update_memory m loc (Some (BorrowMut loc)), VRefMut (RefMut loc))
      | _ => None
      end
  | EImmBorrow loc =>
      match m loc with
      | Some (Own v) =>
          Some (update_memory m loc (Some (BorrowImm (loc :: nil))), VRefImmMut (RefImm loc))
      | Some (BorrowImm l) => 
          Some (update_memory m loc (Some (BorrowImm (loc :: l))), VRefImmMut (RefImm loc))
      | _ => None 
      end
  | EDeref e' =>
      match eval m e' with
        | Some (m', VRefMut loc) =>
            match m (ref_to_mem_loc loc) with
              | Some (OwnMut v) => Some (m', v)
              | _ => None
              end
        | Some (m', VRefImmMut loc) =>
            match m (ref_to_mem_loc loc) with
              | Some (Own v) => Some (m', v) 
              | _ => None 
            end
        | _ => None 
      end
  | ELet x e1 e2 =>
      match eval m e1 with
      | Some (m', v) =>
          let new_m := update_memory m' (MemLoc (var_to_nat x)) (Some (Own v)) in
          eval new_m e2
      | _ => None
      end
  | ESequence e1 e2 =>
      match eval m e1 with
      | Some (m', _) => eval m' e2 
      | _ => None
      end
end.


Inductive borrow_valid : memory_state -> mem_loc -> borrow_state -> Prop :=
  | BorrowMutValid : forall m loc,
      m loc = Some (BorrowMut loc) ->
      borrow_valid m loc (MutBorrowed loc)
  | BorrowImmValid : forall m loc bs,
      m loc = Some (BorrowImm bs) ->
      Forall (fun r => m r = Some (BorrowImm bs)) bs ->
      borrow_valid m loc (ImmBorrowed bs).


Inductive has_type : lifetime_state -> memory_state -> expression -> ref_type -> Prop :=
| TValInt : forall (l : lifetime_state) (m : memory_state) (z : Z),
    has_type l m (EValue (VInt z)) (RefImm (MemLoc 0)) (* Integer literals *)

| TValRefMut : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc),
    has_type l m (EValue (VRefMut (RefMut loc))) (RefMut loc) (* Mutable references *)

| TValRefImm : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc),
    has_type l m (EValue (VRefImmMut (RefImm loc))) (RefImm loc) (* Immutable references *)

| TValUnit : forall (l : lifetime_state) (m : memory_state),
    has_type l m (EValue VUnit) (RefImm (MemLoc 0)) (* Unit type *)
| TVar : forall (l : lifetime_state) (m : memory_state) (x : var) (r : ref_type),
    (* Variable typing requires ownership to be convertible to a reference type *)
    match m (MemLoc (var_to_nat x)) with
    | Some (Own _) => r = RefImm (MemLoc (var_to_nat x))
    | Some (BorrowMut loc) => r = RefMut loc
    | Some (BorrowImm locs) => r = RefImm (MemLoc (var_to_nat x))
    | _ => False (* Invalid case *)
    end ->
    has_type l m (EVar x) r
| TMutBorrow : forall l m x t,
    (* Mutable borrow is valid if the variable has a mutable type *)
    has_type l m (EVar x) (RefMut t) ->
    has_type l m (EMutBorrow (MemLoc (var_to_nat x))) (RefMut t)

| TImmBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
    (* Immutable borrow is valid if the variable has an immutable type *)
    has_type l m (EVar x) (RefImm loc)->
    has_type l m (EImmBorrow (MemLoc (var_to_nat x))) (RefImm loc)

| TMut : forall (l : lifetime_state) (m : memory_state) (x : var) (e : expression) (r : ref_type),
    (* Mutability ensures the binding is treated as mutable *)
    has_type l m e r ->
    has_type l m (EMut x e) r.

Theorem type_safety : 
forall (l : lifetime_state) (m : memory_state) (e : expression) (r : ref_type) (m' : memory_state) (v : value),
 has_type l m e r ->             
  (exists m' v, eval m e = Some (m', v)) \/ eval m e = None.
Proof.
  (* intros l m e r Htype. *)
  intros l m e r m' v Htype.
  generalize dependent v.
  induction e.
  - left. exists m, v. simpl. reflexivity.
  - simpl. destruct (m (MemLoc (var_to_nat v))).
    + destruct o.
      * left. exists m, v0. reflexivity.
      * right. reflexivity.
      * right. reflexivity.
      * left. exists m, v0. reflexivity.
    + right. reflexivity.
  - intros v. inversion Htype.
  - simpl. inversion Htype. subst r. rewrite <- H in *.  destruct (m (MemLoc (var_to_nat x))) eqn:Hlookup.
    + destruct o.
      * left. 
      exists (update_memory m (MemLoc (var_to_nat x)) (Some (BorrowMut (MemLoc (var_to_nat x))))),
      (VRefMut (RefMut (MemLoc (var_to_nat x)))).
reflexivity.
      * right. reflexivity.
      * right. reflexivity.
      * right. reflexivity.
    + right. reflexivity.
  - simpl. inversion Htype. subst r. rewrite <- H in *. destruct (m (MemLoc (var_to_nat x))).
    + destruct o.
      * left. exists (update_memory m (MemLoc (var_to_nat x)) (Some (BorrowImm (MemLoc (var_to_nat x) :: nil)))).
      exists (VRefImmMut (RefImm (MemLoc (var_to_nat x)))). reflexivity.
      * right. reflexivity.
      * left. exists (update_memory m (MemLoc (var_to_nat x)) (Some (BorrowImm (MemLoc (var_to_nat x) :: l1)))).
      exists (VRefImmMut (RefImm (MemLoc (var_to_nat x)))). reflexivity.
      * right. reflexivity.
    + right. reflexivity.
  - inversion Htype.
  - inversion Htype.
  - intros. simpl. inversion Htype.
    destruct (IHe H4) as [[m'' [v' Heval]] | Heval].
    + auto.
    + simpl.
      destruct (m (MemLoc (var_to_nat v))) eqn:Hlookup.
      * (* Case: m (MemLoc (var_to_nat v)) = Some _ *)
        right. reflexivity. (* Borrow fails because the location is already in use *)
      * (* Case: m (MemLoc (var_to_nat v)) = None *)
        destruct v'.
        -- (* Case: v' = VInt z *)
          exists (update_memory m'' (MemLoc (var_to_nat v)) (Some (OwnMut (VInt 0)))).
          exists VUnit.
          reflexivity.
        * (* Case: v' = VRefMut loc *)
          right. reflexivity. (* Borrow fails for invalid value *)
        * (* Case: v' = VRefImm loc *)
          right. reflexivity. (* Borrow fails for invalid value *)
        * (* Case: v' = VUnit *)
          right. reflexivity. (* Borrow fails for invalid value *)
        reflexivity.
    
    
  
  - 
Admitted.

Theorem borrow_safety : 
forall (l : lifetime_state) (m : memory_state) (e: expression) (r : ref_type) (m' : memory_state) (v : value) (loc : mem_loc) (bs : borrow_state),
  has_type l m e r ->         
  borrow_valid m loc bs ->                
  eval m e = Some (m', v) -> 
  borrow_valid m' loc bs.
Proof.
Admitted.


End Exp.