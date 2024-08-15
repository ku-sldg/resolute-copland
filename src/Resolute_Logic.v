(* Encoding of the RESOLUTE logic (and RESOLUTE to Copland translator) in coq *)

Require Export String Maps OptMonad_Coq.
Require Export List.

(* Generic ID Type -- for now, just make it nat *)
Definition ID_Type := nat.

(* Target ID *)
Definition Target_ID := ID_Type.
(* Target Group ID -- some meaningful (but abstract) grouping of targets *)
Definition Target_Group := ID_Type.
(* A concrete set of targets *)
Definition Target_Pool := list Target_ID.

(* ASP (Attestation Service Provider) IDs *)
Definition ASP_ID := ID_Type.

(* Explicit mapping from target groups to pools *)
Definition Target_Map := MapC Target_Group Target_Pool.

(* Explicit mapping from target IDs to the ASP IDs that measure those targets *)
Definition Measures_Map := MapC Target_ID ASP_ID.

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

(* This will probably need more parameters going forward...
   something like a "cert strategy"... *)
Definition cert_policy (appE:AppEvidence) : bool.
Admitted.

Definition end_to_end_cert (t:Term) : bool :=
  cert_policy (appraise (measure t)).

Inductive Resolute : Type :=
  | R_False
  | R_True
  | R_Goal (T : Target_ID)
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute)
  | R_Forall (T : Target_Group)  (G : Target_ID -> Resolute)
  | R_Exists (T : Target_Group) (G : Target_ID -> Resolute).

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

(* Get all ASP_IDs of corresponding Target_IDs in Measures_Map *)
Definition get_aspids (ls:list Target_ID) (mm:Measures_Map) : Opt (list ASP_ID).
Admitted.

(* Construct a compound Term from a list of ASP_IDs *)
Definition aspids_to_term (ls:list ASP_ID) : Term.
Admitted.

Fixpoint res_to_copland (r:Resolute) (mm:Measures_Map) (tm:Target_Map) : Opt Term :=
  match r with 
  | R_False => failm 
  | R_True => ret emptyTerm
  | (R_Goal tid) => 
      i <- (map_get mm tid) ;;
      (ret (aspTerm i))
  | R_And r1 r2 => 
    t1 <- res_to_copland r1 mm tm ;;
    t2 <- res_to_copland r2 mm tm ;;
    ret (seqTerm t1 t2)
  | R_Or r1 r2 => 
    t1 <- res_to_copland r1 mm tm ;;
    t2 <- res_to_copland r2 mm tm ;;
    ret (seqTerm t1 t2)
  | R_Imp r1 r2 => 
    res_to_copland r1 mm tm (* Is generating terms for antecedent enough here? *)
  | R_Forall tg pred => 
    pool <- map_get tm tg ;;
    asp_ids <- (get_aspids pool mm) ;;
    ret (aspids_to_term asp_ids)
  | R_Exists tg pred => 
    pool <- map_get tm tg ;;
    asp_ids <- (get_aspids pool mm) ;;
    ret (aspids_to_term asp_ids)
  end.
 

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
  | Reval_Forall : forall (A:Assumptions) (m:Target_Map) 
    (gr:Target_Group) (tp:Target_Pool) (pred: Target_ID -> Resolute),      
      (forall (v:Target_ID), 
        map_get m gr = Some tp -> 
        In v tp -> 
        Reval A (pred v)) ->
      Reval A (R_Forall gr pred)
  | Reval_Exists : forall (A:Assumptions) (m:Target_Map) 
    (gr:Target_Group) (tp:Target_Pool) (pred: Target_ID -> Resolute),      
      (exists (v:Target_ID), 
        map_get m gr = Some tp -> 
        In v tp -> 
        Reval A (pred v)) ->
      Reval A (R_Exists gr pred).


Theorem res_to_copland_sound : forall (a:Assumptions) (r:Resolute) mm tm, 
  (exists t, 
    (res_to_copland r mm tm = Some t) /\ 
  end_to_end_cert t = true) 
  <->
  Reval a r.
Proof.
Admitted.


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
