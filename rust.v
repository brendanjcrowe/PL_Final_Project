Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.


Module Exp.

Inductive mem_loc : Type :=
| MemLoc : nat -> mem_loc
| InvalidMem : mem_loc.

Definition mem_loc_to_nat (loc : mem_loc) : option nat :=
match loc with
  | MemLoc n => Some n
  | InvalidMem => None
end.


Inductive ref_type : Type :=
| RefMut : mem_loc -> ref_type  
| RefImm : list mem_loc -> ref_type.

Definition ref_to_mem_loc (ref : ref_type) : mem_loc :=
match ref with
| RefMut (MemLoc n) => MemLoc n 
| RefMut (InvalidMem) => InvalidMem 
| RefImm locs => match locs with
  | MemLoc n :: _  => MemLoc n
  | InvalidMem :: _ => InvalidMem 
  | nil => InvalidMem 
  end
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

Definition memory_state := 
mem_loc -> option ownership.

Definition lifetime_state := nat -> nat.

Inductive borrow_state : Type :=
| MutBorrowed : mem_loc -> borrow_state
| ImmBorrowed : list mem_loc -> borrow_state.

Definition eqb_option_nat (o1 o2 : option nat) : bool :=
  match o1, o2 with
  | Some n1, Some n2 => Nat.eqb n1 n2
  | _, _ => false
  end.
  
Definition update_memory (m : memory_state) (loc : mem_loc) (v : option ownership) : memory_state :=
 fun l =>
    if eqb_option_nat (mem_loc_to_nat l) (mem_loc_to_nat loc) then v else m l.

Inductive eval_result : Type :=
| EvalSuccess : memory_state -> value -> eval_result
| EvalError : eval_error -> eval_result
with eval_error : Type :=
| UninitializedMemory : mem_loc -> eval_error
| BorrowConflict : mem_loc -> eval_error
| InvalidAssignment : mem_loc -> eval_error
| TypeMismatch : eval_error
| OtherError : eval_error.

Lemma success_neq_failure :
forall (m : memory_state) (v : value) (err : eval_error ),
EvalSuccess m v <> EvalError err.
Proof.
intros. discriminate. Qed.


Fixpoint eval (m : memory_state) (e : expression) : eval_result :=
match e with
  | EValue v => EvalSuccess m v
  | EVar x =>
    match m (MemLoc (var_to_nat x)) with
    | Some (Own v) => EvalSuccess m v
    | Some (OwnMut v) => EvalSuccess m v
    | Some (BorrowMut loc) => EvalSuccess m (VRefMut (RefMut loc))
    | Some (BorrowImm locs) => EvalSuccess m (VRefImmMut (RefImm (MemLoc (var_to_nat x) :: locs)))
    | None => EvalError (UninitializedMemory (MemLoc (var_to_nat x)))
    end
  | EAssign loc e' =>
    match eval m e' with
      | EvalSuccess m' v =>
          match m loc with
          | Some (OwnMut _) =>
              EvalSuccess (update_memory m' loc (Some (OwnMut v))) v
          | Some _ => EvalError (InvalidAssignment loc)
          | None => EvalError (UninitializedMemory loc)
          end
      | EvalError err => EvalError err
    end
  | EMut x e' =>
      match eval m e' with
      | EvalSuccess m' v =>
          EvalSuccess (update_memory m' (MemLoc (var_to_nat x)) (Some (OwnMut v))) VUnit
      | EvalError err => EvalError err
      end
  | EMutBorrow loc =>
      match m loc with
      | Some (Own v) => EvalSuccess (update_memory m loc (Some (BorrowMut loc))) (VRefMut (RefMut loc))
      | Some _ => EvalError (BorrowConflict loc)
      | None => EvalError (UninitializedMemory loc)
      end
  | EImmBorrow loc =>
      match m loc with
      | Some (Own v) => EvalSuccess (update_memory m loc (Some (BorrowImm (loc :: nil)))) (VRefImmMut (RefImm (loc :: nil)))
      | Some (BorrowImm l) => EvalSuccess (update_memory m loc (Some (BorrowImm (loc :: l)))) (VRefImmMut (RefImm (loc :: l)))
      | Some _ => EvalError (BorrowConflict loc)
      | None => EvalError (UninitializedMemory loc)
      end
  | EDeref e' =>
      match eval m e' with
      | EvalSuccess m' (VRefMut ref) =>
          match m (ref_to_mem_loc ref) with
          | Some (OwnMut v) => EvalSuccess m' v
          | _ => EvalError (BorrowConflict (ref_to_mem_loc ref))
          end
      | EvalSuccess m' (VRefImmMut loc) =>
          match m (ref_to_mem_loc loc) with
          | Some (Own v) => EvalSuccess m' v
          | _ => EvalError (BorrowConflict (ref_to_mem_loc loc))
          end
      | EvalSuccess _ _ => EvalError TypeMismatch
      | EvalError err => EvalError err
      end
  | ELet x e1 e2 =>
      match eval m e1 with
      | EvalSuccess m' v =>
          let new_m := update_memory m' (MemLoc (var_to_nat x)) (Some (Own v)) in
          eval new_m e2
      | EvalError err => EvalError err
      end
  | ESequence e1 e2 =>
      match eval m e1 with
      | EvalSuccess m' _ => eval m' e2
      | EvalError err => EvalError err
      end
end.


Lemma eval_let_immutable :
  forall m,
    eval m (ELet (Var 0) (EValue (VInt 42)) (EVar (Var 0))) =
    EvalSuccess (update_memory m (MemLoc 0) (Some (Own (VInt 42)))) (VInt 42).
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.


Inductive borrow_valid : memory_state -> mem_loc -> borrow_state -> Prop :=
  | BorrowMutValid : forall m loc,
      m loc = Some (BorrowMut loc) ->
      borrow_valid m loc (MutBorrowed loc)
  | BorrowImmValid : forall m loc bs,
      m loc = Some (BorrowImm bs) ->
      Forall (fun r => m r = Some (BorrowImm bs)) bs ->
      borrow_valid m loc (ImmBorrowed bs).


Inductive well_typed : lifetime_state -> memory_state -> expression -> ref_type -> Prop :=
| TValInt : forall (l : lifetime_state) (m : memory_state) (z : Z),
    well_typed l m (EValue (VInt z)) (RefImm (MemLoc 0 :: nil)) 

| TValRefMut : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc),
    well_typed l m (EValue (VRefMut (RefMut loc))) (RefMut loc) 

| TValRefImm : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc),
    well_typed l m (EValue (VRefImmMut (RefImm (loc :: nil)))) (RefImm (loc :: nil)) 

| TValUnit : forall (l : lifetime_state) (m : memory_state),
    well_typed l m (EValue VUnit) (RefImm (MemLoc 0 :: nil))

| TVar : forall (l : lifetime_state) (m : memory_state) (x : var) (r : ref_type),
    match m (MemLoc (var_to_nat x)) with
    | Some (Own _) => r = RefImm (MemLoc (var_to_nat x) :: nil)
    | Some (BorrowMut loc) => r = RefMut loc
    | Some (BorrowImm locs) => r = RefImm (MemLoc (var_to_nat x) :: locs)
    | _ => False 
    end ->
    well_typed l m (EVar x) r
| TMutBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
    well_typed l m (EVar x) (RefMut loc) ->
    well_typed l m (EMutBorrow (MemLoc (var_to_nat x))) (RefMut loc)

| TImmBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
    well_typed l m (EVar x) (RefImm (loc :: nil))->
    well_typed l m (EImmBorrow (MemLoc (var_to_nat x))) (RefImm (loc :: nil))

| TMut : forall (l : lifetime_state) (m : memory_state) (x : var) (e : expression) (r : ref_type),
    well_typed l m e r ->
    well_typed l m (EMut x e) r.

(* Theorem type_safety : 
forall (l : lifetime_state) (m : memory_state) (e : expression) (r : ref_type) (m' : memory_state) (v : value) (err : eval_error),
 well_typed l m e r ->             
  (exists m' v, eval m e = EvalSuccess m' v) \/ eval m e = EvalError err.
Proof.
  (* intros l m e r Htype. *)
  intros l m e r m' v err Htype.
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
        (* right. reflexivity. Borrow fails because the location is already in use *)
      (* * Case: m (MemLoc (var_to_nat v)) = None *)
      (* * destruct v'.
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
        reflexivity. *)
Admitted. *)

Lemma none_some_neq : forall (m : memory_state) (v : value), None <> Some (m, v).
Proof.
  intros m v H.
  discriminate H.
Qed.


Theorem type_safety_2 : 
forall (l : lifetime_state) (m : memory_state) (e : expression) (r : ref_type) (m' : memory_state) (v : value),
 well_typed l m e r ->             
  (exists m' v, eval m e = EvalSuccess m' v).
Proof.
  intros l m e r m' v Htype.
  induction Htype.

  (* Case: TValInt *)
  - exists m, (VInt z). reflexivity.

  (* Case: TValRefMut *)
  - exists m, (VRefMut (RefMut loc)). reflexivity.

  (* Case: TValRefImm *)
  - exists m, (VRefImmMut (RefImm (loc :: nil))). reflexivity.

  (* Case: TValUnit *)
  - exists m, VUnit. reflexivity.

  (* Case: TVar (EVar x) *)
  - intros. simpl. destruct (m (MemLoc (var_to_nat x))) eqn:Hmem.
    + destruct o.
      * exists m, v0. reflexivity.
      * exists m, (VRefMut (RefMut m0)). reflexivity. (* apply none_some_neq with (m := m) (v := v). *)
      * exists m, (VRefImmMut (RefImm (MemLoc (var_to_nat x) :: l0))). reflexivity.
        (* exfalso. assumption. *)
      * exfalso. assumption. 
    + exfalso. assumption. 

  (* Case: TMutBorrow *)
  - destruct (m (MemLoc (var_to_nat x))) eqn:Hmem.
    + destruct o.
      * exists (update_memory m (MemLoc (var_to_nat x)) (Some (BorrowMut (MemLoc (var_to_nat x))))),
               (VRefMut (RefMut (MemLoc (var_to_nat x)))).
        simpl. rewrite Hmem. reflexivity.
      * simpl in *. rewrite Hmem in *.  destruct IHHtype. destruct H. injection H. exists m, v. admit.
      * simpl in *. rewrite Hmem in *. absurd (EvalSuccess m v = EvalError (BorrowConflict (MemLoc (var_to_nat x)))). 
        -- discriminate.
        -- destruct IHHtype. destruct H. admit.
      * exists (update_memory m (MemLoc (var_to_nat x)) (Some (BorrowMut (MemLoc (var_to_nat x))))),
               (VRefMut (RefMut (MemLoc (var_to_nat x)))). simpl. admit.
    +  exists m, v. simpl. rewrite Hmem. admit.

  (* Case: TImmBorrow (EImmBorrow) *)
  - destruct (m (MemLoc (var_to_nat x))) eqn:Hmem.
    + destruct o as [v_mem | v_mem | l_borrowed | v_mem].
      * exists (update_memory m (MemLoc (var_to_nat x)) (Some (BorrowImm (MemLoc (var_to_nat x) :: nil) ))),
              (VRefImmMut (RefImm (MemLoc (var_to_nat x) :: nil))).
        simpl. rewrite Hmem. reflexivity.
      * exists (update_memory m (MemLoc (var_to_nat x))
                              (Some (BorrowMut (MemLoc (var_to_nat x))))),
              (VRefMut (RefMut (MemLoc (var_to_nat x)))).
        simpl in *. rewrite Hmem in *. admit.
      * exists (update_memory m (MemLoc (var_to_nat x))
                              (Some (BorrowImm (MemLoc (var_to_nat x) :: l_borrowed)))),
              (VRefImmMut (RefImm (MemLoc (var_to_nat x) :: l_borrowed))).
        simpl. rewrite Hmem.  reflexivity.
      * exists (update_memory m (MemLoc (var_to_nat x))
                              (Some (BorrowMut (MemLoc (var_to_nat x))))),
              (VRefImmMut (RefImm (MemLoc (var_to_nat x) :: nil))).
        simpl. rewrite Hmem. admit.
    + exists (update_memory m (MemLoc (var_to_nat x))
                                (Some (BorrowMut (MemLoc (var_to_nat x))))),
                (VRefImmMut (RefImm (MemLoc (var_to_nat x) :: nil))).
      simpl. rewrite Hmem. admit.

 (* Case: TMut *)
- simpl. 
  destruct IHHtype as [m'' [v' Heval]].
  exists (update_memory m'' (MemLoc (var_to_nat x)) (Some (OwnMut v'))), VUnit. 

Admitted.



Theorem borrow_safety : 
forall (l : lifetime_state) (m : memory_state) (e: expression) (r : ref_type) (m' : memory_state) (v : value) (loc : mem_loc) (bs : borrow_state),
  well_typed l m e r ->         
  borrow_valid m loc bs ->                
  eval m e = EvalSuccess m' v -> 
  borrow_valid m' loc bs.
Proof.
Admitted.


End Exp.