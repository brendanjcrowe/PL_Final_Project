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

Lemma success_neq_failure :
forall (m : memory_state) (v : value) (err : eval_error ),
EvalSuccess m v <> EvalError err. 
Proof.
intros. discriminate. Qed.


Inductive eval : memory_state -> expression -> eval_result -> Prop :=
| EVal : forall (m : memory_state) (v : value),
    eval m (EValue v) (EvalSuccess m v)
| EVarOwnSuccess : forall (m : memory_state) (x : var) (v : value),
    m (MemLoc (var_to_nat x)) = Some (Own v) ->
    eval m (EVar x) (EvalSuccess m v)

| EVarMutSuccess : forall (m : memory_state) (x : var) (v : value),
    m (MemLoc (var_to_nat x)) = Some (OwnMut v) ->
    eval m (EVar x) (EvalSuccess m v)

| EVarBorrowMut : forall (m : memory_state) (x : var) (loc : mem_loc),
    m (MemLoc (var_to_nat x)) = Some (BorrowMut loc) ->
    eval m (EVar x) (EvalSuccess m (VRefMut (RefMut loc)))

| EVarBorrowImm : forall (m : memory_state) (x : var) (locs : list mem_loc),
    m (MemLoc (var_to_nat x)) = Some (BorrowImm locs) ->
    eval m (EVar x) (EvalSuccess m (VRefImmMut (RefImm locs)))

| EVarError : forall (m : memory_state) (x : var),
    m (MemLoc (var_to_nat x)) = None ->
    eval m (EVar x) (EvalError (UninitializedMemory (MemLoc (var_to_nat x))))

| EAssignSuccess : forall (m m' : memory_state) (loc : mem_loc) (e : expression) (v : value),
    eval m e (EvalSuccess m' v) ->
    m loc = Some (OwnMut v) ->
    eval (update_memory m' loc (Some (OwnMut v))) (EAssign loc e) (EvalSuccess (update_memory m' loc (Some (OwnMut v))) v)

| EAssignError : forall (m : memory_state) (loc loc' : mem_loc) (locs : list mem_loc) (v : value) (e : expression) (err : eval_error),
    eval m e (EvalError err ) -> 
    m loc = None ->
    eval m (EAssign loc e) (EvalError err)

| EMutBorrowSuccess : forall (m : memory_state) (loc : mem_loc) (v : value),
    m loc = Some (Own v) ->
    eval (update_memory m loc (Some (BorrowMut loc))) 
         (EMutBorrow loc) 
         (EvalSuccess (update_memory m loc (Some (BorrowMut loc))) (VRefMut (RefMut loc)))

| EMutBorrowError : forall (m : memory_state) (loc : mem_loc),
    m loc = None ->
    eval m (EMutBorrow loc) (EvalError (UninitializedMemory loc))

| EImmBorrowSuccess : forall (m : memory_state) (loc : mem_loc) (locs : list mem_loc) (v : value),
    m loc = Some (Own v) ->
    eval (update_memory m loc (Some (BorrowImm (locs)))) 
         (EImmBorrow loc) 
         (EvalSuccess (update_memory m loc (Some (BorrowImm (locs))))
         (VRefImmMut (RefImm (locs))))

| EImmBorrowConflict : forall (m : memory_state) (loc : mem_loc),
    m loc = Some (BorrowMut loc) ->
    eval m (EImmBorrow loc) (EvalError (BorrowConflict loc))

| EDerefMutSuccess : forall (m m' : memory_state) (e : expression) (loc : mem_loc) (v : value),
    eval m e (EvalSuccess m' (VRefMut (RefMut loc))) ->
    m loc = Some (OwnMut v) ->
    eval m e (EvalSuccess m' v)

| EDerefImmSuccess : forall (m m' : memory_state) (e : expression) (locs : list mem_loc) (v : value),
    eval m e (EvalSuccess m' (VRefImmMut (RefImm locs))) ->
    m (hd InvalidMem locs) = Some (Own v) ->
    eval m e (EvalSuccess m' v)

| ELetSuccess : forall (m m' m'' : memory_state) (x : var) (e1 e2 : expression) (v1 v2 : value),
    eval m e1 (EvalSuccess m' v1) ->
    eval (update_memory m' (MemLoc (var_to_nat x)) (Some (Own v1))) e2 (EvalSuccess m'' v2) ->
    eval m (ELet x e1 e2) (EvalSuccess m'' v2)

| ESequenceSuccess : forall (m m' m'' : memory_state) (e1 e2 : expression) (v1 v2 : value),
    eval m e1 (EvalSuccess m' v1) ->
    eval m' e2 (EvalSuccess m'' v2) ->
    eval m (ESequence e1 e2) (EvalSuccess m'' v2)
    
| EMutSuccess : forall (m m' : memory_state) (x : var) (e : expression) (v : value),
    eval m e (EvalSuccess m' v) -> 
    eval (update_memory m' (MemLoc (var_to_nat x)) (Some (OwnMut v))) 
         (EMut x e) 
         (EvalSuccess (update_memory m' (MemLoc (var_to_nat x)) (Some (OwnMut v))) VUnit).

Inductive borrow_valid : memory_state -> mem_loc -> borrow_state -> Prop :=
  | BorrowMutValid : forall (m : memory_state) (loc : mem_loc),
      m loc = Some (BorrowMut loc) ->
      borrow_valid m loc (MutBorrowed loc)
  | BorrowImmValid : forall (m : memory_state) (loc : mem_loc) (locs : list mem_loc),
      m loc = Some (BorrowImm locs) ->
      Forall (fun l => m l = Some (BorrowImm locs)) locs ->
      In loc locs ->
      borrow_valid m loc (ImmBorrowed locs).


Inductive well_typed : lifetime_state -> memory_state -> expression -> ref_type -> Prop :=
| TValUnit : forall (l : lifetime_state) (m : memory_state),
  eval m (EValue (VUnit)) (EvalSuccess m VUnit) ->
  well_typed l m (EValue VUnit) (RefImm (MemLoc 0 :: nil))

| TValInt : forall (l : lifetime_state) (m : memory_state) (z : Z),
  eval m (EValue (VInt z)) (EvalSuccess m (VInt z)) ->
  well_typed l m (EValue (VInt z)) (RefImm (MemLoc 0 :: nil)) 

| TValRefImm : forall (l : lifetime_state) (m : memory_state) (locs : list mem_loc),
  eval m (EValue (VRefImmMut (RefImm (locs)))) (EvalSuccess m (VRefImmMut (RefImm (locs))) )->
  well_typed l m (EValue (VRefImmMut (RefImm (locs)))) (RefImm (locs))

| TValRefMut : forall (l : lifetime_state) (m : memory_state) (loc : mem_loc),
  eval m (EValue (VRefMut (RefMut loc))) (EvalSuccess m (VRefMut (RefMut loc))) ->
  well_typed l m (EValue (VRefMut (RefMut loc))) (RefMut loc)

| TVarOwn : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
  eval m (EVar x) (EvalSuccess m (VRefImmMut ( RefImm (loc :: nil)))) -> 
  well_typed l m (EVar x) (RefImm (loc :: nil))

| TVarOwnMut : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
  eval m (EVar x) (EvalSuccess m (VRefMut (RefMut (MemLoc (var_to_nat x))))) -> 
  well_typed l m (EVar x) (RefMut (MemLoc (var_to_nat x)))

| TVarBorrowImm : forall (l : lifetime_state) (m : memory_state) (x : var) (locs : list mem_loc),
  eval m (EVar x) (EvalSuccess m (VRefImmMut (RefImm (locs)))) -> 
  well_typed l m (EVar x) (RefImm (locs))

| TVarBorrowMut : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
  eval m (EVar x) (EvalSuccess m (VRefMut (RefMut (loc)))) -> 
  well_typed l m (EVar x) (RefMut (loc))

| TAssign : forall (l : lifetime_state) (m m' : memory_state) (v : value) (loc : mem_loc) (e : expression),
    eval m (EAssign loc e) (EvalSuccess (update_memory m' loc (Some (OwnMut v))) v) ->
    well_typed l m (EAssign loc e) (RefMut loc)

| TImmBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (locs : list mem_loc) (loc : mem_loc),
  eval m (EImmBorrow loc) (EvalSuccess (update_memory m loc (Some (BorrowImm (locs))))
         (VRefImmMut (RefImm (locs)))) -> 
    well_typed l m (EImmBorrow (loc)) (RefImm (locs))

| TMutBorrow : forall (l : lifetime_state) (m : memory_state) (x : var) (loc : mem_loc),
    eval m (EMutBorrow loc) 
         (EvalSuccess (update_memory m loc (Some (BorrowMut loc))) (VRefMut (RefMut loc))) ->
    well_typed l m (EMutBorrow (loc)) (RefMut loc)

| TDerefImm: forall (l : lifetime_state) (m m' : memory_state) (v : value) (e: expression) (locs : list mem_loc),
    eval m (EDeref e) (EvalSuccess m' v) ->
    well_typed l m (EDeref e) (RefImm locs)
  
| TDerefMut : forall (l : lifetime_state) (m m': memory_state) (v : value) (e : expression) (loc : mem_loc),
    eval m (EDeref e) (EvalSuccess m' v) ->
    well_typed l m (EDeref e) (RefMut loc)
  
| TLet : forall (l : lifetime_state) (m m' m'': memory_state) (v1 v2 : value) (x : var) (e1 e2 : expression) (r1 r2 : ref_type),
    eval m e1 (EvalSuccess m' v1) ->
    well_typed l (update_memory m' (MemLoc (var_to_nat x)) (Some (Own v1))) e2 r2 ->
    eval m (ELet x e1 e2) (EvalSuccess m'' v2) ->
    well_typed l m (ELet x e1 e2) r2

| TSequence : forall (l : lifetime_state) (m m' m'' : memory_state) (e1 e2 : expression) (v1 v2 : value) (r2 : ref_type),
    eval m e1 (EvalSuccess m' v1) ->
    well_typed l m' e2 r2 ->
    eval m (ESequence e1 e2) (EvalSuccess m'' v2) ->
    well_typed l m (ESequence e1 e2) r2

| TMut : forall (l : lifetime_state) (m m' : memory_state) (x : var) (e e' : expression) (v : value),
    eval m (EMut x e') (EvalSuccess (update_memory m' (MemLoc (var_to_nat x)) (Some (OwnMut v))) VUnit) -> 
    well_typed l m (EMut x e') (RefMut (MemLoc (var_to_nat x))).


Theorem type_safety : 
forall (l : lifetime_state) (m : memory_state) (e : expression) (r : ref_type) (m' : memory_state) (v : value),
 well_typed l m e r ->             
  (exists m' v, eval m e (EvalSuccess m' v)).
Proof.
  intros l m e r m' v Htype.
  induction Htype.

  (* Case: TValUnit *)
  - exists m, VUnit. assumption.

  (* Case: TValInt *)
  - exists m, (VInt z). assumption.

  (* Case: TValRefImm *)
  - exists m, (VRefImmMut (RefImm (locs))). assumption.

  (* Case: TValRefMut *)
  - exists m, (VRefMut (RefMut loc)). assumption.

  (* Case: TVarOwn (EVar x) *)
  - exists m, (VRefImmMut (RefImm (loc :: nil))). assumption.
  - exists m, (VRefMut (RefMut (MemLoc (var_to_nat x)))).  assumption.
  - exists m, (VRefImmMut (RefImm locs)). assumption.
  - exists m, (VRefMut (RefMut loc)). assumption.
  - exists (update_memory m'0 loc (Some (OwnMut v0))), v0. assumption.
  - exists (update_memory m loc (Some (BorrowImm (locs)))) , (VRefImmMut (RefImm locs)). assumption.
  - exists (update_memory m loc (Some (BorrowMut loc))), (VRefMut (RefMut loc)). assumption.
  - exists m'0, v0. assumption.
  - exists m'0, v0. assumption.
  - exists m'', v2. assumption.
  - exists m'', v2. assumption.
  - exists (update_memory m'0 (MemLoc (var_to_nat x)) (Some (OwnMut v0))), VUnit. assumption.
Qed.

Theorem weak_borrow_safety :
  forall (m : memory_state) (loc : mem_loc) (state : borrow_state),
    borrow_valid m loc state ->
    match state with
    | MutBorrowed loc' =>
        (* A mutable borrow must be unique *)
        forall other_state, m loc' = Some other_state -> other_state = BorrowMut loc'
    | ImmBorrowed locs =>
        (* All references to a single memory location must be accounted for *)
        Forall (fun l => exists bs, m l = Some (BorrowImm bs) /\ In l bs) locs
    end.
Proof.
   intros m loc state Hvalid.
   induction Hvalid as [m loc H | m loc locs HSome HForall].
    - intros other_state Hlookup.
      rewrite H in Hlookup.
      inversion Hlookup; subst.
      reflexivity.
   - pose proof (proj1 (Forall_forall (fun l => m l = Some (BorrowImm locs)) locs)) as Hforall_impl.
      specialize (Hforall_impl).
      apply Forall_forall.
      exists locs.
      split.
      + apply Hforall_impl.
       * exact HForall.
       * assumption.
      + assumption.
Qed.


End Exp.