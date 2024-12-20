Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.EqNat.
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
| VRefImmMut : ref_type -> value
| VRefMut : ref_type -> value.


Inductive var : Type := 
| Var : nat -> var. 

Definition var_to_nat (v : var) : nat :=
match v with
  | Var n => n
end.

Inductive expression : Type :=
| EValue: value -> expression (* 10; *)                  
| EVar : var -> expression (* a; *)                           
| EAssign : mem_loc -> expression -> expression (* a = 10; *)
| EImmBorrow : mem_loc -> expression (* b = &a; *)  
| EMutBorrow : mem_loc -> expression (* b = &a; *)               
| EDeref : expression -> expression (* *a *)               
| ELet : var -> expression -> expression -> expression (* let a = 10;a;*)
| EMut : var -> expression -> expression (* let mut a = 10; *)
| ESequence : expression -> expression -> expression.  (* let mut a 10; a = 5;*)       


Inductive ownership : Type :=
| Own : value -> ownership 
| OwnMut : value -> ownership
| BorrowImm : list mem_loc -> ownership
| BorrowMut : mem_loc ->  ownership.      



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
  
Definition update_memory (m : memory_state) (loc : mem_loc) (o : option ownership) : memory_state :=
fun l => 
    if eqb_option_nat (mem_loc_to_nat l) (mem_loc_to_nat loc) 
    then o else m l.

Inductive eval_result : Type :=
| EvalSuccess : memory_state -> value -> eval_result
| EvalError : eval_error -> eval_result
with eval_error : Type :=
| UninitializedMemory : mem_loc -> eval_error
| BorrowConflict : mem_loc -> eval_error
| InvalidAssignment : mem_loc -> eval_error
| TypeMismatch : eval_error
| OtherError : eval_error.

Inductive eval_result_2 : Type :=
| EvalSuccess2 
| EvalError2.




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
    | Some (BorrowImm locs) => EvalSuccess m (VRefImmMut (RefImm locs))
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
| EImmBorrow loc =>
  match m loc with
  | Some (Own v) => EvalSuccess (update_memory m loc (Some (BorrowImm (loc :: nil)))) (VRefImmMut (RefImm (loc :: nil)))
  | Some (BorrowImm l) => EvalSuccess (update_memory m loc (Some (BorrowImm (loc :: l)))) (VRefImmMut (RefImm (loc :: l)))
  | Some _ => EvalError (BorrowConflict loc)
  | None => EvalError (UninitializedMemory loc)
  end
| EMutBorrow loc =>
    match m loc with
    | Some (Own v) => EvalSuccess (update_memory m loc (Some (BorrowMut loc))) (VRefMut (RefMut loc))
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
| EMut x e' =>
  match eval m e' with
  | EvalSuccess m' v =>
      EvalSuccess (update_memory m' (MemLoc (var_to_nat x)) (Some (OwnMut v))) VUnit
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
  | BorrowMutValid : forall (m : memory_state) (loc : mem_loc),
      m loc = Some (BorrowMut loc) ->
      borrow_valid m loc (MutBorrowed loc)
  | BorrowImmValid : forall (m : memory_state) (loc : mem_loc) (locs : list mem_loc),
      m loc = Some (BorrowImm locs) ->
      Forall (fun l => m l = Some (BorrowImm locs)) locs ->
      borrow_valid m loc (ImmBorrowed locs).


Inductive well_typed : lifetime_state -> memory_state -> expression -> ref_type -> Prop :=

| TValUnit : forall (l : lifetime_state) (m : memory_state),
  eval m (EValue (VUnit)) = EvalSuccess m (VUnit) ->
  well_typed l m (EValue VUnit) (RefImm (MemLoc 0 :: nil))
| TValInt : forall (l : lifetime_state) (m : memory_state) (z : Z),
  eval m (EValue (VInt z)) = EvalSuccess m (VInt z) ->
  well_typed l m (EValue (VInt z)) (RefImm (MemLoc 0 :: nil)) 

| TValRefImm : forall (l : lifetime_state) (m : memory_state) (locs : list mem_loc),
  eval m (EValue (VRefImmMut (RefImm (locs)))) = EvalSuccess m (VRefImmMut (RefImm (locs))) ->
  well_typed l m (EValue (VRefImmMut (RefImm (locs)))) (RefImm (locs)) 
| TValRefMut : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc),
  eval m (EValue (VRefMut (RefMut loc))) = EvalSuccess m (VRefMut (RefMut loc)) ->
  well_typed l m (EValue (VRefMut (RefMut loc))) (RefMut loc) 

| TVar : forall (l : lifetime_state) (m : memory_state) (x : var) (r : ref_type),
    eval m (EVar x) = 
    match m (MemLoc (var_to_nat x)) with
    | Some (Own _) => EvalSuccess m (VRefImmMut ( RefImm (MemLoc (var_to_nat x) :: nil)))
    | Some (OwnMut _) => EvalSuccess m (VRefMut ( RefMut (MemLoc (var_to_nat x))))
    | Some (BorrowImm locs) => EvalSuccess m (VRefImmMut (RefImm (locs)))
    | Some (BorrowMut loc) => EvalSuccess m (VRefMut (RefMut loc ))
    | None => EvalError (UninitializedMemory (MemLoc (var_to_nat x)))
    end ->
    well_typed l m (EVar x) r
| TAssign : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc) (e : expression),
    well_typed l m e (RefMut loc) ->
    well_typed l m (EAssign loc e) (RefMut loc)
| TImmBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (locs : list mem_loc),
    well_typed l m (EVar x) (RefImm (locs))->
    well_typed l m (EImmBorrow (MemLoc (var_to_nat x))) (RefImm (locs))
| TMutBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
    well_typed l m (EVar x) (RefMut loc) ->
    well_typed l m (EMutBorrow (MemLoc (var_to_nat x))) (RefMut loc)
| TDerefImm : forall (l : lifetime_state) (m : memory_state) (e: expression) (loc : list mem_loc),
    well_typed l m e (RefImm loc) ->
    well_typed l m (EDeref e) (RefImm loc)
| TDerefMut : forall (l : lifetime_state) (m : memory_state) (e : expression) (loc : mem_loc),
    well_typed l m e (RefMut loc) ->
    well_typed l m (EDeref e) (RefMut loc)
| TLet : forall (l : lifetime_state) (m : memory_state) (x : var) (e1 e2 : expression) (r1 r2 : ref_type),
    well_typed l m e1 r1 ->
    well_typed l (update_memory m (MemLoc (var_to_nat x)) (Some (Own (VInt 0)))) e2 r2 ->
    well_typed l m (ELet x e1 e2) r2
| TMut : forall (l : lifetime_state) (m : memory_state) (x : var) (e : expression) (r : ref_type),
    well_typed l m e r ->
    well_typed l m (EMut x e) r
| TSequence : forall (l : lifetime_state) (m : memory_state) (e1 e2 : expression) (r : ref_type),
    well_typed l m e1 r ->
    well_typed l m e2 r ->
    well_typed l m (ESequence e1 e2) r.

Lemma eval_value :
  forall (l : lifetime_state) (m : memory_state) (v : value) (r : ref_type),
  well_typed l m (EValue v) r ->
  exists m' v', eval m (EValue v) = EvalSuccess m' v'.
Proof.
  intros l m v r H.
  destruct v; try (exists m, v; reflexivity).
  - (* VUnit *)
    exists m, VUnit. reflexivity.
  - (* VInt z *)
    exists m, (VInt z). reflexivity.
  - (* VRefImmMut ref *) 
    exists m, (VRefImmMut (r0)). reflexivity.
  - (* VRefImmMut ref *)
    exists m, (VRefMut (r0)). reflexivity.
Qed.

Lemma eval_var :
  forall (l : lifetime_state) (m : memory_state) (x : var) (r : ref_type),
  well_typed l m (EVar x) r ->
  exists v', eval m (EVar x) = EvalSuccess m v'.
Proof.
  intros l m x r H.
  destruct (m (MemLoc (var_to_nat x))); try (exists m, VUnit; reflexivity).
  - destruct o as [own | ownmut | borrowimm locs | borrowmut loc ]; try (exists m, VUnit; reflexivity).
  + (* Some (Own v) *) destruct own.
    --  simpl. inversion H. subst.  exists VUnit. admit.
    -- admit. (* Some (OwnMut v) *)
    -- admit.
    -- admit.
    + admit.
  Admitted.

Lemma eval_assign :
  forall (l : lifetime_state) (m : memory_state) (loc : mem_loc) (e : expression) (r : ref_type),
  well_typed l m (EAssign loc e) r ->
  exists m' v', eval m (EAssign loc e) = EvalSuccess m' v'.
Proof.
  intros l m loc e r H.

Admitted.

(* Theorem type_safety : 
forall (l : lifetime_state) (m : memory_state) (e : expression) (r : ref_type) (m' : memory_state) (v : value),
 well_typed l m e r ->             
  (exists m' v, eval m e = EvalSuccess m' v).
Proof.
    intros l m e r H.
     induction e; intros; try (apply eval_value in H0; assumption).
  - apply eval_var in H0. exists m. assumption.
  -  apply eval_assign in H0. assumption.
  - ass
   *)

Theorem type_safety : 
forall (l : lifetime_state) (m : memory_state) (e : expression) (r : ref_type) (m' : memory_state) (v : value),
 well_typed l m e r ->             
  (exists m' v, eval m e = EvalSuccess m' v).
Proof.
  intros l m e r m' v Htype.
  induction Htype.

  (* Case: TValUnit *)
  - exists m, VUnit. reflexivity.

  (* Case: TValInt *)
  - exists m, (VInt z). reflexivity.

  (* Case: TValRefImm *)
  - exists m, (VRefImmMut (RefImm (locs))). reflexivity.

  (* Case: TValRefMut *)
  - exists m, (VRefMut (RefMut loc)). reflexivity.

  (* Case: TVar (EVar x) *)
  - intros. simpl. destruct (m (MemLoc (var_to_nat x))) eqn:Hmem.
    + destruct o.
      * exists m, v0. reflexivity.
      * exists m, v0. reflexivity.
      * exists m, (VRefImmMut (RefImm (l0))). reflexivity.
      * exists m, (VRefMut (RefMut m0)). reflexivity. (* apply none_some_neq with (m := m) (v := v). *)
    (* exfalso. assumption. *)
    +  destruct (m (MemLoc (var_to_nat x))) eqn:Hmem2.
    * (* Case: m (MemLoc (var_to_nat x)) = Some o *) discriminate Hmem.  (* Analyze valid memory states *)
    * exists m, v. simpl in H. rewrite Hmem2 in H. exfalso.
    apply success_neq_failure with
    (err := UninitializedMemory (MemLoc (var_to_nat x)))
    (m := m') (v := v). 
    assert (EvalError (UninitializedMemory (MemLoc (var_to_nat x))) <> EvalSuccess m' v).
      {
        (* Step 3: Use distinctness of constructors *)
        intros Hcontra. discriminate Hcontra. (* EvalError and EvalSuccess are distinct *)
      }
    admit.
    

  - admit.
  

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
  - (* Case: TDerefImm *) admit.
  - (* Case: TDerefMut*) admit.
  - (* Case: TLet*) admit.
  - (* Case: TMut*)simpl. 
    destruct IHHtype as [m'' [v' Heval]].
    exists (update_memory m'' (MemLoc (var_to_nat x)) (Some (OwnMut v'))), VUnit.  admit.
  - (* Case: TSeq*)admit.
  (* Case: TMut *)
Admitted.



Theorem borrow_safety : 
forall (l : lifetime_state) (m : memory_state) (e: expression) (r : ref_type) (m' : memory_state) (v : value) (loc : mem_loc) (bs : borrow_state),
  well_typed l m e r ->         
  borrow_valid m loc bs ->                
  eval m e = EvalSuccess m' v -> 
  borrow_valid m' loc bs.
Proof.
  intros l m e r m' v loc bs HType.
Admitted.


End Exp.