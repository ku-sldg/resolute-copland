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
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute).

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
  | Reval_Or : forall A G1 G2,
    (Reval A G1) \/ (Reval A G2) -> Reval A (R_Or G1 G2)
  | Reval_Imp : forall A G1 G2,
    Reval (G1::A) G2 -> Reval A (R_Imp G1 G2).

Example test0 :
  Reval ((R_And (Rfalse) (Rtrue))::nil) (R_And (Rfalse) (Rtrue)).
Proof.
  apply Reval_And.
  - apply Reval_L. admit.
  - apply Reval_R.
Abort.

Example test1 :
  Reval (nil) (R_Or (Rfalse) (Rtrue)).
Proof.
  apply Reval_Or. right. apply Reval_R.
Qed.

Example test2 :
  Reval (nil) (R_Imp (Rfalse) (Rtrue)).
Proof.
  apply Reval_Imp. apply Reval_R.
Qed.








