(* Encoding of the RESOLUTE logic (and RESOLUTE to Copland translator) in coq *)

Require Export String Maps.
Require Export List.

Import ListNotations.

(* Generic ID Type -- for now, just make it nat *)
Definition ID_Type := nat.

(* Target ID *)
Definition Target_ID := ID_Type.

(* ASP (Attestation Service Provider) IDs *)
Definition ASP_ID := ID_Type.

(* Explicit mapping from target IDs to the ASP IDs that measure those targets *)
Definition Measures_Map := MapC Target_ID ASP_ID.

(* Copland Term (or Copland phrase) -- Representation of Copland attestation protocols *)
Inductive Term : Type := 
| emptyTerm : Term
| aspTerm : ASP_ID -> Term
| seqTerm : Term -> Term -> Term.

Inductive Evidence : Type := 
| emptyE : Evidence
| aspE : ASP_ID -> Evidence
| seqE : Evidence -> Evidence -> Evidence.

Inductive AppEvidence : Type := 
| app_emptyE : AppEvidence
| app_aspE : ASP_ID -> AppEvidence 
| app_seqE : AppEvidence -> AppEvidence -> AppEvidence.

(* Abstract system measurement -- vastly simplified simulation 
   of the Copland Virtual Machine (CVM) *)
Fixpoint measure (t:Term) : Evidence := 
  match t with 
  | emptyTerm => emptyE
  | aspTerm i => aspE i 
  | seqTerm t1 t2 => seqE (measure t1) (measure t2)
  end.

(* Abstract appraisal procedure *)
Fixpoint appraise (e:Evidence) : AppEvidence := 
  match e with
  | emptyE => app_emptyE
  | aspE i => app_aspE i 
  | seqE e1 e2 => app_seqE (appraise e1) (appraise e2)
  end.

Inductive Resolute : Type :=
  | R_False
  | R_True
  | R_Goal (T : Target_ID)
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute)
  | R_Forall (l : list Target_ID)  (G : Target_ID -> Resolute)
  | R_Exists (l : list Target_ID) (G : Target_ID -> Resolute).

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

Record Model := {
  conc : Target_ID -> Term ;
  spec : Target_ID -> list AppEvidence
}.

Fixpoint res_to_copland (M : Model) (r:Resolute) : Term * (AppEvidence -> Prop) :=
  match r with 
  | R_False => (emptyTerm, fun e => False)

  | R_True => (emptyTerm, fun e => True)

  | (R_Goal tid) => (conc M tid, fun e => In e (spec M tid))

  | R_And r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 in
    let '(t2, pol2) := res_to_copland M r2 in
    (seqTerm t1 t2, fun e => pol1 e /\ pol2 e)

  | R_Or r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 in
    let '(t2, pol2) := res_to_copland M r2 in
    (seqTerm t1 t2, fun e => pol1 e \/ pol2 e)

  | R_Imp r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 in
    let '(t2, pol2) := res_to_copland M r2 in
    (seqTerm t1 t2, fun e => pol1 e -> pol2 e)

  | R_Forall l pred => 
    (* forall x \in l, do pred l *)
    let list_tpols := map (fun x => res_to_copland M (pred x)) l in
    fold_left (fun x y => (seqTerm (fst x) (fst y), fun e => (snd x) e /\ (snd y) e)) list_tpols (emptyTerm, fun e => True)

  | R_Exists l pred => 
    (* exists x \in l, do pred l *)
    let list_tpols := map (fun x => res_to_copland M (pred x)) l in
    fold_left (fun x y => (seqTerm (fst x) (fst y), fun e => (snd x) e \/ (snd y) e)) list_tpols (emptyTerm, fun e => False)
  end.
 

Inductive Reval : Assumptions -> Resolute -> Prop :=
  | Reval_L : forall A G,
    In R_False A -> Reval (A) G
  | Reval_R : forall A,
    Reval A R_True
  (*
    1. Is using In and appending the new assumption helpful?
    2. Naming: "Left" (L) and "Right" (R) have been used in earlier versions
    to refer to the left and right of a split.
    I have changed them to match how SLC uses left and right to refer to
    the left (antecedent) and right (consequent) sides of a sequent,
    which is also how left and right are used on other sources such as Wikipedia.
    https://slc.openlogicproject.org/slc-screen.pdf
    How do we want to name these rules for best clarity?
  *)
  | Reval_And_L1 : forall a1 a2 A G,
    (In a1 A) -> (Reval A G) -> (Reval ((R_And a1 a2)::A) G)
  | Reval_And_L2 : forall a1 a2 A G,
    (In a2 A) -> (Reval A G) -> (Reval ((R_And a1 a2)::A) G)
  | Reval_And_R : forall A G1 G2,
    Reval A G1 -> Reval A G2 -> Reval A (R_And G1 G2)
  | Reval_Or_L : forall a1 a2 A G,
    (In a1 A) -> (In a2 A) -> (Reval A G) -> (Reval ((R_Or a1 a2)::A) G)
  | Reval_Or_R1 : forall A G1 G2,
    (Reval A G1) -> Reval A (R_Or G1 G2)
  | Reval_Or_R2 : forall A G1 G2,
    (Reval A G2) -> Reval A (R_Or G1 G2)
  | Reval_Imp : forall A G1 G2,
    Reval (G1::A) G2 -> Reval A (R_Imp G1 G2)
  | Reval_Forall : forall (A:Assumptions) 
    (tp:list Target_ID) (pred: Target_ID -> Resolute),      
      (forall (v:Target_ID), 
        In v tp -> 
        Reval A (pred v)) ->
      Reval A (R_Forall tp pred)
  | Reval_Exists : forall (A:Assumptions)
    (tp:list Target_ID) (pred: Target_ID -> Resolute),      
      (exists (v:Target_ID), 
        In v tp -> 
        Reval A (pred v)) ->
      Reval A (R_Exists tp pred).

Theorem res_to_copland_sound : forall (m:Model) (r:Resolute),
  (forall t pol, res_to_copland m r=(t,pol) -> pol (appraise (measure t)))
  <->
  (forall a, Reval a r).
Proof.
  intros. split; intros H.
  - induction r.
    (* R_False: solved *)
    + intros. specialize H with (t := emptyTerm) (pol := fun x => False). 
      simpl in H. destruct H. reflexivity.
    (* R_True: solved *)
    + intros. apply Reval_R. 
    (* R_Goal: in progress *)
    (* I think this the most important section of the proof that is incomplete,
    because I think the other cases require some similar logic. 
    What is needed here is to be able to use the hypothesis
    implies that an arbitrary goal can be evaluated in Reval.
    It is not clear to me yet how to use the hypothesis in this way. 
    *)
    + intros. specialize H with (t := conc m T).
    simpl in H. specialize H with (pol := fun e => In e (spec m T)).
    simpl in H. intros. admit.
    (* Reval_And: in progress *)
    + intros. apply Reval_And_R.
      -- apply IHr1. intros t pol. intros H1. apply H. admit.
      -- admit.
    (* Reval_Or: in progress *)
    + intros. apply Reval_Or_R1. admit.
    (* Reval_Imp: in progress *)
    + intros. apply Reval_Imp. admit.
    (* Reval_Forall: in progress *)
    + intros. apply Reval_Forall. admit.
    (* Reval_Exists: in progress *)
    + intros. apply Reval_Exists. admit.
    (* This part of the proof is much less developed. *)
  - induction t.
    (* app_emptyE : in progress *)
    + intros. simpl. admit. (* Axiom for app_emptyE? *)
    (* Here I think we need a mirror to the problem for the RGoal T case,
    that being that to prove that an arbitrary ASP complies with the policy
    if Reval succeeds.
    *)
    (* app_aspE : in progress *)
    + intros. simpl. admit.
    (* app_seqE : in progress *) 
    + intros. simpl. admit. (* Recurse on pol *)
Admitted.

Example test_RAnd :
  Reval ((R_And (R_False) (R_True))::nil) (R_And (R_False) (R_True)).
Proof.
  apply Reval_And_R.
  - apply Reval_L. unfold In. left. admit.
  - apply Reval_R.
Admitted.

Example test_ROr :
  Reval (nil) (R_Or (R_False) (R_True)).
Proof.
  apply Reval_Or_R2. apply Reval_R.
Qed.

Example test_RImp :
  Reval (nil) (R_Imp (R_False) (R_True)).
Proof.
  apply Reval_Imp. apply Reval_R.
Qed.



(*
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
*)
