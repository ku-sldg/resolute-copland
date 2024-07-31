(* Encoding of the RESOLUTE logic in coq *)

Require Export String.
Require Export List.

(*
Inductive Formula : Type :=
  | false
  | true
  | Var : string -> Formula
  | Not : Formula -> Formula
  | Impl : Formula -> Formula -> Formula.
*)

(*
Inductive FinTypeElems : Set := 
| FinType1_Elems
| FinType2_Elems.
*)


Definition FinSet : Set.  Admitted.
(*
Inductive FinSet : Set :=
| Threads
| Memories.

Inductive FixedThreadPool : Set := 
| Thread1
| Thread2
| ThreadBob.
*)


Definition FinSetElements (T:FinSet) : Set.  Admitted.
(*
Definition FinSetElements (T:FinSet) : Set :=
  match T with
  | Threads => FixedThreadPool
  | Memories => list nat
  end.
*)

Inductive Resolute : Type :=
  | R_False
  | R_True
  | R_Goal (T : FinSet)
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute)
  | R_Forall (T: FinSet) (G : (FinSetElements T) -> Resolute)
  | R_Exists (T : FinSet) (G : (FinSetElements T) -> Resolute).

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

(*
Inductive Reval : Assumptions -> Resolute -> Prop :=
  | eval_L (A : Assumptions) (e : Assumption) (G : Resolute) :
    e = R_Goal false -> Reval (e::A) G
  | eval_R (A : Assumptions) (G : Resolute) :
    G = R_Goal true -> Reval A G
  | R_And_eval (A : Assumptions) (G1 G2 : Resolute) : 
    Reval A G1 -> Reval A G2 -> Reval A (R_And G1 G2).
*)

Inductive Reval : Assumptions -> Resolute -> Prop :=
  | Reval_L : forall A G,
    In R_False A -> Reval (A) G
  | Reval_R : forall A,
    Reval A R_True
  | Reval_And : forall A G1 G2,
    Reval A G1 -> Reval A G2 -> Reval A (R_And G1 G2)
  | Reval_Or_L : forall A G1 G2,
    (Reval A G1) -> Reval A (R_Or G1 G2)
  | Reval_Or_R : forall A G1 G2,
    (Reval A G2) -> Reval A (R_Or G1 G2)
  | Reval_Imp : forall A G1 G2,
    Reval (G1::A) G2 -> Reval A (R_Imp G1 G2)
  | Reval_Forall{T:FinSet} : forall (A:Assumptions) (pred: (FinSetElements T) -> Resolute),      
      (forall (v:FinSetElements T), Reval A (pred v)) ->
      Reval A (R_Forall T pred)
  | Reval_Exists{T:FinSet} : forall (A:Assumptions) (pred: (FinSetElements T) -> Resolute),
      (exists (v:FinSetElements T), Reval A (pred v)) -> 
      Reval A (R_Exists T pred).
    (*
  | Reval_Forall_nil : forall A G,
    Reval A (R_Forall nil G)
  | Reval_Forall : forall A n ns G,
    Reval A (G n) -> Reval A (R_Forall ns G) -> Reval A (R_Forall (n::ns) G)
    
  | Reval_Exists_skip : forall A n ns G,
    Reval A (R_Exists ns G) -> Reval A (R_Exists (n::ns) G)
  | Reval_Exists : forall A n ns G,
    Reval A (G n) -> Reval A (R_Exists (n::ns) G).
    *)

Example test_RAnd :
  Reval ((R_And (R_False) (R_True))::nil) (R_And (R_False) (R_True)).
Proof.
  apply Reval_And.
  - apply Reval_L. unfold In. left. admit.
  - apply Reval_R.
Admitted.

Example test_ROr :
  Reval (nil) (R_Or (R_False) (R_True)).
Proof.
  apply Reval_Or_R. apply Reval_R.
Qed.

Example test_RImp :
  Reval (nil) (R_Imp (R_False) (R_True)).
Proof.
  apply Reval_Imp. apply Reval_R.
Qed.

Example test_RForall :
  Reval (nil) (R_Forall (5 :: (2 :: (3 :: nil))) (R_Goal)).
Proof.
  apply Reval_Forall. admit.
  apply Reval_Forall. admit.
  apply Reval_Forall. admit.
  apply Reval_Forall_nil.
Admitted.

Example test_RExists :
  Reval (nil) (R_Exists (5 :: (2 :: (3 :: nil))) (R_Goal)).
Proof.
  apply Reval_Exists_skip. apply Reval_Exists. admit.
Admitted.
