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

Inductive Resolute : Type :=
  | Rfalse
  | Rtrue
  | Goal (n : nat)
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute)
  | R_Forall (ns : list nat) (G : nat -> Resolute)
  | R_Exists (ns : list nat) (G : nat -> Resolute).

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

(*
Inductive Reval : Assumptions -> Resolute -> Prop :=
  | eval_L (A : Assumptions) (e : Assumption) (G : Resolute) :
    e = Goal false -> Reval (e::A) G
  | eval_R (A : Assumptions) (G : Resolute) :
    G = Goal true -> Reval A G
  | R_And_eval (A : Assumptions) (G1 G2 : Resolute) : 
    Reval A G1 -> Reval A G2 -> Reval A (R_And G1 G2).
*)

Inductive Reval : Assumptions -> Resolute -> Prop :=
  | Reval_L : forall A e G,
    e = Rfalse -> Reval (e::A) G
  | Reval_R : forall A,
    Reval A Rtrue
  | Reval_And : forall A G1 G2,
    Reval A G1 -> Reval A G2 -> Reval A (R_And G1 G2)
  | Reval_Or_L : forall A G1 G2,
    (Reval A G1) -> Reval A (R_Or G1 G2)
  | Reval_Or_R : forall A G1 G2,
    (Reval A G2) -> Reval A (R_Or G1 G2)
  | Reval_Imp : forall A G1 G2,
    Reval (G1::A) G2 -> Reval A (R_Imp G1 G2)
  | Reval_Forall_nil : forall A G,
    Reval A (R_Forall nil G)
  | Reval_Forall : forall A n ns G,
    Reval A (G n) -> Reval A (R_Forall ns G) -> Reval A (R_Forall (n::ns) G)
  | Reval_Exists_skip : forall A n ns G,
    Reval A (R_Exists ns G) -> Reval A (R_Exists (n::ns) G)
  | Reval_Exists : forall A n ns G,
    Reval A (G n) -> Reval A (R_Exists (n::ns) G).

Example test_RAnd :
  Reval ((R_And (Rfalse) (Rtrue))::nil) (R_And (Rfalse) (Rtrue)).
Proof.
  apply Reval_And.
  - apply Reval_L. admit.
  - apply Reval_R.
Admitted.

Example test_ROr :
  Reval (nil) (R_Or (Rfalse) (Rtrue)).
Proof.
  apply Reval_Or_R. apply Reval_R.
Qed.

Example test_RImp :
  Reval (nil) (R_Imp (Rfalse) (Rtrue)).
Proof.
  apply Reval_Imp. apply Reval_R.
Qed.

Example test_RForall :
  Reval (nil) (R_Forall (5 :: (2 :: (3 :: nil))) (Goal)).
Proof.
  apply Reval_Forall. admit.
  apply Reval_Forall. admit.
  apply Reval_Forall. admit.
  apply Reval_Forall_nil.
Admitted.

Example test_RExists :
  Reval (nil) (R_Exists (5 :: (2 :: (3 :: nil))) (Goal)).
Proof.
  apply Reval_Exists_skip. apply Reval_Exists. admit.
Admitted.











