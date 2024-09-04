(* Encoding of the RESOLUTE logic (and RESOLUTE to Copland translator) in coq *)

Require Export String Maps.
Require Export List EqClass.
Require Import StructTactics.

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

Fixpoint eqb_term `{EqClass ASP_ID} (t1 t2 : Term) : bool :=
  match t1, t2 with
  | emptyTerm, emptyTerm => true
  | aspTerm a1, aspTerm a2 => eqb a1 a2
  | seqTerm t11 t12, seqTerm t21 t22 =>
    eqb_term t11 t21 && eqb_term t12 t22
  | _, _ => false
  end.

Global Instance EqClass_Term : EqClass Term.
eapply Build_EqClass with (eqb := eqb_term).
induction x, y; ff;
repeat rewrite PeanoNat.Nat.eqb_eq in *;
ff;
repeat rewrite Bool.andb_true_iff in *;
ff; try split;
repeat erewrite IHx1 in *;
repeat erewrite IHx2 in *;
ff.
Defined.

Inductive Evidence : Type := 
| emptyE : Evidence
| aspE : ASP_ID -> Evidence
| seqE : Evidence -> Evidence -> Evidence.

Fixpoint eqb_Evidence `{EqClass ASP_ID} (e1 e2 : Evidence) : bool :=
  match e1, e2 with
  | emptyE, emptyE => true
  | aspE a1, aspE a2 => eqb a1 a2
  | seqE e11 e12, seqE e21 e22 => 
    eqb_Evidence e11 e21 && 
    eqb_Evidence e12 e22
  | _, _ => false
  end.

Global Instance EqClass_Evidence : EqClass Evidence.
eapply Build_EqClass with (eqb := eqb_Evidence).
induction x, y; ff;
repeat rewrite PeanoNat.Nat.eqb_eq in *;
ff;
repeat rewrite Bool.andb_true_iff in *;
ff; try split;
repeat erewrite IHx1 in *;
repeat erewrite IHx2 in *;
ff.
Defined.

Inductive AppEvidence : Type := 
| app_emptyE : AppEvidence
| app_aspE : ASP_ID -> AppEvidence 
| app_seqE : AppEvidence -> AppEvidence -> AppEvidence.

Fixpoint eqb_AppEvidence `{EqClass ASP_ID} (e1 e2 : AppEvidence) : bool :=
  match e1, e2 with
  | app_emptyE, app_emptyE => true
  | app_aspE a1, app_aspE a2 => eqb a1 a2
  | app_seqE e11 e12, app_seqE e21 e22 => 
    eqb_AppEvidence e11 e21 && 
    eqb_AppEvidence e12 e22
  | _, _ => false
  end.

Global Instance EqClass_AppEvidence : EqClass AppEvidence.
eapply Build_EqClass with (eqb := eqb_AppEvidence).
induction x, y; ff;
repeat rewrite PeanoNat.Nat.eqb_eq in *;
ff;
repeat rewrite Bool.andb_true_iff in *;
ff; try split;
repeat erewrite IHx1 in *;
repeat erewrite IHx2 in *;
ff.
Defined.
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
  | R_Forall (l : list Target_ID) (fn : string)
    (* (G : Target_ID -> Resolute) *)
  | R_Exists (l : list Target_ID) (fn : string).
  (* (G : Target_ID -> Resolute). *)

Fixpoint eqb_Resolute `{EqClass string, EqClass (list Target_ID)} (r1 r2 : Resolute) : bool :=
  match r1, r2 with
  | R_False, R_False => true
  | R_True, R_True => true
  | R_Goal t1, R_Goal t2 => eqb t1 t2
  | R_And g11 g12, R_And g21 g22 =>
    eqb_Resolute g11 g21 && eqb_Resolute g12 g22
  | R_Or g11 g12, R_Or g21 g22 =>
    eqb_Resolute g11 g21 && eqb_Resolute g12 g22
  | R_Imp g11 g12, R_Imp g21 g22 =>
    eqb_Resolute g11 g21 && eqb_Resolute g12 g22
  | R_Forall l1 f1, R_Forall l2 f2 =>
    eqb f1 f2 && eqb l1 l2
  | R_Exists l1 f1, R_Exists l2 f2 =>
    eqb f1 f2 && eqb l1 l2
  | _, _ => false
  end.

Instance EqClass_Resolute `{EqClass string, EqClass (list Target_ID)}
  : EqClass Resolute.
eapply Build_EqClass with (eqb := eqb_Resolute).
induction x, y; ff;
repeat rewrite PeanoNat.Nat.eqb_eq in *;
ff;
repeat rewrite Bool.andb_true_iff in *;
ff; try split;
repeat erewrite IHx1 in *;
repeat erewrite IHx2 in *;
ff;
repeat rewrite eqb_eq in *; ff.
Defined.

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

Record Model := {
  fns   : MapC string (Target_ID -> Resolute) ;
  conc  : Target_ID -> Term ;
  spec  : Target_ID -> (AppEvidence -> Prop) ;
  (* list AppEvidence *)
}.

Fixpoint res_to_copland `{Heq : EqClass Resolute} (M : Model) 
    (A : Assumptions) (r:Resolute) {struct r}
    : Term * (AppEvidence -> Prop) :=
  (* check r \in assumptions *)
  if (in_dec (EqClass_impl_DecEq _) r A)
  then (emptyTerm, fun e => True)
  else
  match r with 
  | R_False => (emptyTerm, fun e => False)

  | R_True => (emptyTerm, fun e => True)

  | (R_Goal tid) => (conc M tid, spec M tid)
  (* fun e => In e (spec M tid)) *)

  | R_And r1 r2 => 
    let '(t1, pol1) := res_to_copland M A r1 in
    let '(t2, pol2) := res_to_copland M A r2 in
    (seqTerm t1 t2, fun e => 
      match e with
      | app_seqE e1 e2 => pol1 e1 /\ pol2 e2
      | _ => False
      end)

  | R_Or r1 r2 => 
    let '(t1, pol1) := res_to_copland M A r1 in
    let '(t2, pol2) := res_to_copland M A r2 in
    (seqTerm t1 t2, fun e => 
      match e with
      | app_seqE e1 e2 => pol1 e1 \/ pol2 e2
      | _ => False
      end)

  | R_Imp r1 r2 => 
    let '(t1, pol1) := res_to_copland M A r1 in
    let '(t2, pol2) := res_to_copland M (r1 :: A) r2 in
    (seqTerm t1 t2, fun e => 
      match e with
      | app_seqE e1 e2 => pol1 e1 -> pol2 e2
      | _ => False
      end)

  | R_Forall l fnName => 
    (* forall x \in l, do pred l *)
    match map_get (fns M) fnName with
    | None => (emptyTerm, fun e => False)
    | Some fn =>
    let list_tpols := map (fun x => res_to_copland M A (fn x)) l in
    fold_left (fun x y => (seqTerm (fst x) (fst y), (fun e => 
      match e with
      | app_seqE e1 e2 => (snd x) e1 /\ (snd y) e2
      | _ => False
      end))) list_tpols (emptyTerm, fun e => True)
    end

  | R_Exists l fnName => 
    (* exists x \in l, do pred l *)
    match map_get (fns M) fnName with
    | None => (emptyTerm, fun e => False)
    | Some fn =>
    let list_tpols := map (fun x => res_to_copland M A (fn x)) l in
    fold_left (fun x y => (seqTerm (fst x) (fst y), (fun e => 
      match e with
      | app_seqE e1 e2 => (snd x) e1 \/ (snd y) e2
      | _ => False
      end))) list_tpols (emptyTerm, fun e => False)
    end
  end.

Lemma thing : forall A B,
  {A} + {~ A} ->
  {B} + {~ B} ->
  {A -> B} + {~ (A -> B)}.
Proof.
  intuition.
Qed.

Lemma thing2 : forall A B,
  A \/ ~ A ->
  B \/ ~ B ->
  (A -> B) \/ (~ (A -> B)).
Proof.
  intuition.
Qed.

Theorem fold_left_ind : forall A B (f : A -> B -> A) l start P P',
  P start ->
  (forall a b, P a -> P' b -> P (f a b)) ->
  (forall b, In b l -> P' b) ->
  P (fold_left f l start).
Proof.
  induction l; ff.
  eapply IHl; ff.
Qed.

(* NOTE: If we can get something stronger out of this,
we will be able to prove DECIDABILITY, stronger than LEM *)
Theorem map_spec : forall A B (f : A -> B) l b,
  In b (map f l) ->
  exists a, f a = b.
Proof.
  induction l; ff.
Qed.

(*

Theorem LEM_appr_proc : forall M r t pol,
  res_to_copland M r = (t, pol) ->
  pol (appraise (measure t)) \/ ~ pol (appraise (measure t)).
Proof.
  induction r; simpl in *; ff.
  - edestruct in_dec;
    try (eapply EqClass_impl_DecEq; eapply EqClass_AppEvidence);
    ff.
  - try pose proof (IHr1 _ _ eq_refl);
    try pose proof (IHr2 _ _ eq_refl);
    destruct H, H0; ff;
    right; intros HC; ff.
  - try pose proof (IHr1 _ _ eq_refl);
    try pose proof (IHr2 _ _ eq_refl);
    destruct H, H0; ff;
    right; intros HC; ff.
  - try pose proof (IHr1 _ _ eq_refl);
    try pose proof (IHr2 _ _ eq_refl);
    ff.
    eapply thing2; ff.
  - (* need lemma that says if 
    P start ->
    (forall fn x, P x -> P (fn x)) ->
    P (fold_left start fn)
  *)
    pose proof (fold_left_ind (Term * (AppEvidence  -> Prop)) _ (fun x y =>
      (seqTerm (fst x) (fst y), (fun e => match e with
        | app_seqE e1 e2 => snd x e1 /\ snd y e2
        | _ => False
      end))) (map (fun x => res_to_copland M (G x)) l) (emptyTerm, fun _ => True) (fun '(t', pol') => pol' (appraise (measure t')) \/ ~ pol'(appraise (measure t'))) (fun '(t', pol') => pol' (appraise (measure t')) \/ ~ pol'(appraise (measure t')))).
    simpl in *.
    setoid_rewrite H0 in X.
    eapply X; ff.
    * destruct X1, X0; ff;
      right; intros HC; ff. 
    * eapply map_spec in H1;
      ff.
  - pose proof (fold_left_ind (Term * (AppEvidence  -> Prop)) _ (fun x y =>
      (seqTerm (fst x) (fst y), (fun e => match e with
        | app_seqE e1 e2 => snd x e1 \/ snd y e2
        | _ => False
      end))) (map (fun x => res_to_copland M (G x)) l) (emptyTerm, fun _ => True) (fun '(t', pol') => pol' (appraise (measure t')) \/ ~ pol'(appraise (measure t'))) (fun '(t', pol') => pol' (appraise (measure t')) \/ ~ pol'(appraise (measure t')))).
    simpl in *.
    setoid_rewrite H0 in X.
    eapply X; ff.
    * right; intros HC; ff.
    * eapply map_spec in H1;
      ff. 
Qed.
*)

Inductive Reval : Assumptions -> Resolute -> Prop :=
  | Reval_L : forall A G,
    In R_False A -> Reval (A) G
  | Reval_R : forall A,
    Reval A R_True
  | Reval_Back : forall G A a',
    In a' A ->
    Reval (a' :: A) G ->
    Reval A G
    (* In G A -> Reval A G *)
  | Reval_And : forall A G1 G2,
    Reval A G1 -> Reval A G2 -> Reval A (R_And G1 G2)
  | Reval_Or_L : forall A G1 G2,
    (Reval A G1) -> Reval A (R_Or G1 G2)
  | Reval_Or_R : forall A G1 G2,
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
Global Hint Constructors Reval : core.

(* Definition consistent (A:Assumptions) : Prop :=
  forall G, In G A -> 
    Reval A G.
  forall G, Reval A G -> G = R_True.

Lemma reval_or_spec : forall A,
  () *)

Lemma reval_or_spec : forall A G1 G2,
  Reval A (R_Or G1 G2) <->
  Reval A G1 \/ Reval A G2.
Proof.
  split; intros; ff;
  prep_induction H;
  induction H; ff;
  pose proof (IHReval _ _ eq_refl); ff.
Qed.

Lemma reval_and_spec : forall A G1 G2,
  Reval A (R_And G1 G2) <->
  Reval A G1 /\ Reval A G2.
Proof.
  split; intros; ff;
  prep_induction H;
  induction H; ff;
  pose proof (IHReval _ _ eq_refl); ff.
Qed.

(*

Theorem Reval_ext : forall G A A',
  (forall a, In a A -> In a A') ->
  Reval A G ->
  Reval A' G.
Proof.
  induction G; ff;
  try (pose proof (IHG1 _ _ H);
    pose proof (IHG2 _ _ H); ff).
  - generalize dependent A'.
    induction H0; ff.
    * eapply IHReval; ff. 
    * eapply Reval_Imp.
      eapply IHReval; ff.
    * eapply Reval_Exists.
      eexists; ff.
      eapply H in H1.
      clear H.
      set (X := pred x) in *.

    *  
    invc H0;
    try (eapply Reval_L; ff; fail);
    try (eapply Reval_Back; ff; fail).
    eapply Reval_Back.
    eapply 
  - invc H0;
    try (eapply Reval_L; ff; fail);
    try (eapply Reval_Refl; ff; fail).
    eapply Reval_Imp.
    eapply IHG2;
    try (eapply H3); ff.
  - invc H1;
    try (eapply Reval_L; ff; fail);
    try (eapply Reval_Refl; ff; fail).
    eapply Reval_Forall;
    ff.
  - invc H1;
    try (eapply Reval_L; ff; fail);
    try (eapply Reval_Refl; ff; fail).
    eapply Reval_Exists;
    ff.
Qed.
*)

Lemma in_r_false_A : forall l,
  {In R_False l} + {~ (In R_False l)}.
Proof.
  induction l; ff.
  destruct IHl; ff. 
  destruct a; ff;
  right; intros HC; ff.
Qed.

Lemma in_r_goal_A : forall t l,
  {In (R_Goal t) l} + {~ (In (R_Goal t) l)}.
Proof.
  induction l; ff.
  destruct IHl; ff. 
  destruct a; ff;
  try (right; intros HC; ff; fail);
  destruct (PeanoNat.Nat.eq_dec t T);
  ff; right; intros HC; ff.
Qed.

(* 

Theorem LEM_reval : forall A r,
  Reval A r \/ ~ Reval A r.
Proof.
  induction r; ff.
  - destruct (in_r_false_A A); ff.
    right; intros HC.
    inversion HC; ff.
  - destruct (in_r_goal_A T A); ff.
    destruct (in_r_false_A A); ff.
    right; intros HC.
    inversion HC; ff.
  - destruct IHr1, IHr2; ff;
    right; intros HC; 
    inversion HC; ff.
    * left; ff.
*)

Axiom in_spec_reval : forall M T,
  spec M T (appraise (measure (conc M T))) <->
  (* In (appraise (measure (conc m T))) (spec m T) <-> *)
  (forall a, Reval a (R_Goal T)).

(*

Lemma reval_trans : forall A r1,
  Reval A r1 ->
  forall r2,
  Reval (r1 :: A) r2 ->
  Reval A r2.
Proof.
  intros A r1 H.
  induction H; ff. 
  - admit. 
  - admit. 
  - admit. 
  - induction r2; ff;
    invc H0; ff.
    * invc H0; ff. 
    *  
  induction r1; ff.
  - clear H.
    induction H0; ff.
    *  
  intros A r1 H.
  induction H; ff.
  - invc H; eauto. 

Lemma reval_cons : forall A r A' A'',
  Reval A r ->
  Reval (A' ++ A ++ A'') r.
Proof.
  induction r; ff;
  try (invc H; try (eapply Reval_L; repeat rewrite in_app_iff; ff; fail);
    try (eapply Reval_Refl; repeat rewrite in_app_iff; ff; fail); ffa; fail).
  - 
    invc H; try (eapply Reval_L; repeat rewrite in_app_iff; ff; fail);
    try (eapply Reval_Refl; repeat rewrite in_app_iff; ff; fail).
    eapply Reval_Imp; ff.
    * eapply Reval_L; ff.
    *  
*)
Axiom decidable_appr_proc : forall P t,
  {P (appraise (measure t))} + {~ P (appraise (measure t))}.

Theorem res_to_copland_sound : forall (m:Model) (r:Resolute) t pol,
  res_to_copland m r = (t,pol) -> 
  pol (appraise (measure t)) ->
  forall A,

  (* forall A,
    (forall a t' pol', 
      In a A ->
      res_to_copland m a = (t', pol') -> 
      pol' (appraise (measure t'))
    ) -> *)
  Reval A r.
Proof.
  induction r; simpl in *; intuition;
  repeat find_eapply_hyp_hyp;
  repeat find_injection; simpl in *;
  intuition.
  - eapply in_spec_reval; eauto. 
  - repeat break_match; repeat find_injection;
    simpl in *; intuition.
    pose proof (IHr1 _ _ eq_refl H).
    pose proof (IHr2 _ _ eq_refl H1).
    eauto.
    (* pose proof (IHr1 _ _ eq_refl H _ H1).
    pose proof (IHr2 _ _ eq_refl H2 _ H1).
    eauto. *)
  - repeat break_match; repeat find_injection;
    simpl in *; intuition;
    try pose proof (IHr1 _ _ eq_refl H);
    try pose proof (IHr2 _ _ eq_refl H2);
    eauto.
  - repeat break_match; repeat find_injection;
    simpl in *; intuition.
    try pose proof (IHr1 _ _ eq_refl H);
    try pose proof (IHr2 _ _ eq_refl H2);
    eauto. 
    destruct (decidable_appr_proc P t0);
    destruct (decidable_appr_proc P0 t1);
    eauto.
    admit.
  - pose proof (fold_left_ind _ _ (fun x y : Term * (AppEvidence -> Prop) => (seqTerm (fst x) (fst y),
fun e : AppEvidence => match e with
| app_seqE e1 e2 => snd x e1 /\ snd y e2
| _ => False
end)) (map (fun x => res_to_copland m (G x)) l) (emptyTerm, (fun _ => True)) (fun '(t, pol) => pol (appraise (measure t))) (fun '(t, pol) => pol (appraise (measure t)))); simpl in *.
repeat find_rewrite.
simpl in *.
intuition.
  eapply Reval_Forall.
  intuition.
  eapply H; ff.
    intros.
    eapply H0; eauto.
  pose proof (fold_left_ind).
    pose proof thing. 
    pose proof thing2.
    intuition; ff.
    * pose proof (IHr1 _ _ eq_refl p _ H1).
      find_eapply_hyp_hyp; eauto.
      eapply Reval_Imp.
      eapply Reval_Refl.
  -  
    eauto.
    simpl in *.
    unfold measure in H.
    simpl in *.


  try (pose proof (H _ _ eq_refl); simpl in *; intuition).
  - eapply Reval_R. 
  - eapply in_spec_reval in H1; eauto.
  - repeat break_match; intuition. 
  split.
  - induction r; simpl in *; intuition;
    try pose proof (H _ _ eq_refl);
    simpl in *; intuition.
    * eapply Reval_R.
    * eapply in_spec_reval; eauto. 
    * eapply Reval_And;
      repeat break_match.
      ** pose proof (H _ _ eq_refl); simpl in *;
        intuition. 
        pose proof (IHr1 t P).
        eapply IHr2 in H2.
  induction r.
  -  
  - pose proof (H _ _ eq_refl). 
    simpl in *; intuition.
  - repeat find_injection. 
    pose proof (H nil); invc H0;
    invc H1.
  -  
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
    + intros. apply Reval_And.
      -- apply IHr1. intros t pol. intros H1. apply H. destruct t.
      -- admit.
    (* Reval_Or: in progress *)
    + intros. apply Reval_Or_L. admit.
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
