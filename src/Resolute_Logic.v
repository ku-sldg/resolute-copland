(* Encoding of the RESOLUTE logic (and RESOLUTE to Copland translator) in coq *)

Require Export String Maps EqClass.
Require Export List.

Require Import Term_Defs_Core.

Import ListNotations.

Definition Arg : Set := nat.

Definition TargetT : Set := nat.
(* Choosing a placeholder definition until a better definition can be made. *)
Definition TargetT : Set := nat.
(* Choosing a placeholder definition until a better definition can be made. *)

Inductive Resolute : Type :=
  | R_False
  | R_True
  | R_Goal (t : TargetT) (l: list Arg)
  | R_And (G1 : Resolute) (G2 : Resolute)
  | R_Or (G1 : Resolute) (G2 : Resolute)
  | R_Imp (G1 : Resolute) (G2 : Resolute)
  (*
  | R_Forall (ls:list TargetT)  (G : TargetT -> Resolute)
  | R_Exists (ls:list TargetT) (G : TargetT -> Resolute).
  *)
.

Definition Assumption := Resolute.
Definition Assumptions := list (Assumption).

(* Extending Assumptions operation (Comma operator in Sequent Calculus).  
   Leaving its implementation abstract for now... *)
Definition Comma (ls:Assumptions) (ls':Assumptions) : Assumptions.
Admitted.

Fixpoint All_In {T : Type} (ls1: list T) (ls2 : list T) : Prop :=
match ls1 with
| h::t => (In h ls2) /\ (All_In t ls2)
| nil => True
end.

Inductive Reval : Assumptions -> Resolute -> Prop :=
  | Reval_L : forall A R,
    In R_False A -> Reval A R

  | Reval_R : forall A,
    Reval A R_True

  | Reval_ID : forall A R, 
    Reval (Comma A [R]) R

  | Reval_ID_List : forall A R, 
    In R A -> Reval A R

  | Reval_ID_Simple : forall R, 
    Reval [R] R

  | Reval_Weaken_Assumptions : forall A B R,
  Reval B R -> Reval (A::B) R

  | Reval_Reverse_Assumptions : forall A R,
  Reval (rev A) R -> Reval A R

  | Reval_Take_One_Assumption : forall A B R,
  Reval [A] R -> Reval (A::B) R
 
  | Reval_And_Intro : forall A R1 R2,
    Reval A R1 -> Reval A R2 -> Reval A (R_And R1 R2)
  
  | Reval_And_Elim : forall A R1 R2 R3,  
    Reval (Comma A [R1;R2]) R3 -> 
    Reval (Comma A [(R_And R1 R2)]) R3

  | Reval_Or_Intro_L : forall A R1 R2,
    (Reval A R1) -> Reval A (R_Or R1 R2)

  | Reval_Or_Intro_R : forall A R1 R2,
    (Reval A R2) -> Reval A (R_Or R1 R2)

  | Reval_Or_Elim : forall A R1 R2 R3, 
    Reval (Comma A [R1]) R3 -> 
    Reval (Comma A [R2]) R3 -> 
    Reval (Comma A [R_Or R1 R2]) R3

  | Reval_Imp_Intro : forall A R1 R2, 
    Reval (Comma A [R1]) R2 -> 
    Reval A (R_Imp R1 R2)

  | Reval_Imp_Elim : forall A R1 R2 R3, 
    Reval A R1 -> 
    Reval (Comma A [R2]) R3 -> 
    Reval (Comma A [R_Imp R1 R2]) R3.

    (*
  | Reval_Forall_Intro : forall (A:Assumptions) 
    (tp:list TargetT) (pred: TargetT -> Resolute),      
      (forall (v:TargetT), 
        In v tp -> 
        Reval A (pred v)) ->
      
      Reval A (R_Forall tp pred)

  | Reval_Forall_Elim : forall (A:Assumptions) 
      (tp:list TargetT) (pred: TargetT -> Resolute) R3,    
        (forall (v:TargetT), 
          In v tp -> 
          Reval (Comma A [pred v]) R3) -> 

        Reval (Comma A [(R_Forall tp pred)]) R3

  | Reval_Exists_Intro : forall (A:Assumptions)
    (tp:list TargetT) (pred: TargetT -> Resolute),      
      (exists (v:TargetT), 
        In v tp -> 
        Reval A (pred v)) ->
      Reval A (R_Exists tp pred)

  | Reval_Exists_Elim : forall (A:Assumptions)
    (tp:list TargetT) (pred: TargetT -> Resolute) R3,      
      (exists (v:TargetT), 
        In v tp -> 
        Reval (Comma A [(pred v)]) R3) ->
      Reval (Comma A [(R_Exists tp pred)]) R3.

    *)

Open Scope string.

Definition mt_ASP_ID : ASP_ID := "mtTerm".
Definition mt_Plc : Plc := "mtPlc".
Definition mt_TARG_ID : Plc := "mtTarg".

Close Scope string.

Definition mtTerm : Term := 
  asp (ASPC (asp_paramsC mt_ASP_ID [] mt_Plc mt_TARG_ID)).


Record Model := {
  conc : TargetT -> Term ;
  spec : TargetT -> (Evidence -> bool)
}.

Global Instance EqClass_TargetT : EqClass TargetT.
Admitted.

(*
Inductive Evidence :=
| evc: RawEv -> EvidenceT -> Evidence.
*)


Definition split_t1 (e:Evidence) : (* option *) Evidence.  (* :=
  match e with 
  | evc rawEv et => 
    match et with 
    | split_evt et1 et2 => 
      let n := et_size et1 in 
      rawEv1 <- peel_n rawEv n ;;
      ret (evc rawEv1 et1)
    | _ => None
    end 
  end.
*)
Admitted.

Definition split_t2 (e:Evidence) : Evidence.
Admitted.

Fixpoint res_to_copland (M : Model) (r:Resolute) (m:Map TargetT Evidence) 
  : Term * (Evidence -> bool) :=
  match r with 
  | R_False => (mtTerm, fun _ => false)
  | R_True =>  (mtTerm, fun _ => true)

  | (R_Goal tid args) => 
     match (map_get tid m) with 
     | None => (conc M tid, fun e => (spec M tid e))
     | Some e => (mtTerm, fun _ => (spec M tid e))
     end

  | R_And r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 m in
    let '(t2, pol2) := res_to_copland M r2 m in
    ((bseq (NONE,NONE) t1 t2), fun e => 
      andb (pol1 (split_t1 e)) (pol2 (split_t2 e)))
    
    (* andb (pol1 e) (pol2 e)) *)

  | R_Or r1 r2 => 
    let '(t1, pol1) := res_to_copland M r1 m in
    let '(t2, pol2) := res_to_copland M r2 m in
    (bseq (NONE,NONE) t1 t2, fun e => orb (pol1 e) (pol2 e))

  | R_Imp r1 r2 => 
    (* TODO:  should we check assumptions/prior evidence cache here? *)
    let '(t1, pol1) := res_to_copland M r1 m in 
    (* let '(t2, pol2) := res_to_copland M r2 m in *)
    (t1(* bseq (NONE,NONE) t1 t2 *), fun e => (*pol1 e -> *) pol1 e)
    end.

 
Definition test_model := {| 
  conc := fun _ => mtTerm;
  spec := fun _ => (fun _ => true)
|}.

(*
	annex resolute {**
			
		goal Data_Wellformed(comp_context : component, property_id : string, filter : component, conn : connection, message_type : data) <=
			** "The Consumer shall only receive well-formed messages" **
			strategy S1 : "Model-based decomposition";
			filter_added(comp_context, filter, conn, message_type)
      NOTE: WHAT ARE STRATEGIES?
		
		-- Top-level claim for proper insertion of a filter
		goal filter_added(comp_context : component, filter : component, conn : connection, msg_type : data) <=
			** "Filter " filter " is properly added to component " comp_context **
			strategy S3 : "Reason over architecture";
			filter_exists(filter, comp_context, conn) and filter_not_bypassed(filter, comp_context, msg_type) and filter_implemented(filter)	

		-- Check to see if there is a filter immediately before the component on the communication pathway.
		goal filter_exists(filter : component, comp_context : component, conn : connection) <=
			** filter " is connected to component " comp_context " by connection " conn **
			let conns : {connection} = {c for (c : connections(comp_context)) | destination_component(c) = comp_context and source_component(c) = filter};
			is_filter(filter) and exists(c : conns) . c = conn
      NOTE: THIS CONTAINS LET STATEMENTS AND EXISTS
			
		-- Make sure there is no communication pathway that avoids the filter
		goal filter_not_bypassed(filter : component, comp_context : component, msg_type : data) <=
			** "Filter " filter " cannot be bypassed" **
			let filter_srcs : {component} = get_filter_sources(comp_context, filter, msg_type); 
			let non_filter_srcs : {component} = get_non_filter_sources(comp_context, filter, msg_type); 
			length(intersect(filter_srcs, non_filter_srcs)) = 0
      NOTE: THIS CONTAINS LET STATEMENTS
			
		-- This provides evidence that the filter was correctly generated for the appropriate OS
	   goal  filter_implemented(filter : component) <=
		    ** "Filter property implemented" **
			implementation_language_assurance(filter)
		   
		-- Checks if the specified component is a filter
		is_filter(c : component) : bool =
			has_property(c, Filter_Properties::Component_Type) and property(c, Filter_Properties::Component_Type) = "FILTER"
			
		get_non_filter_sources(target : component, filter : component, msg_type : data) : {component} = 
			let srcs : {component} = {c for (conn : connections (target)) (c : source_component(conn)) | has_type(conn) and type(conn) = msg_type and not (name(source_component(conn)) = name (filter))}; 
			recursive_backwards_reach(srcs)
      NOTE: THIS CONTAINS LET STATEMENTS
		
		get_filter_sources(target : component, filter : component, msg_type : data) : {component} = 
			let srcs : {component} = {c for (conn : connections(target)) (c : source_component(conn)) | has_type(conn) and type(conn) = msg_type and name(source_component(conn)) = name(filter)};
			prev_reach(srcs)
      NOTE: THIS CONTAINS LET STATEMENTS
		
		recursive_backwards_reach(curr : {component}) : {component} = 
			let prev : {component} = union(curr, prev_reach(curr)); 
			if prev = curr then 
				curr
			else 
				recursive_backwards_reach(prev)
      NOTE: THIS CONTAINS LET STATEMENTS AND A CONDITIONAL?
		
		prev_reach(curr : {component}) : {component} = 
			{y for (x : curr) (y : backwards_reachable_components(x))}
    NOTE: THIS CONTAINS A FORALL, OR WHAT ELSE IS THE FOR SYNTAX?
		
		backwards_reachable_components(comp : component) : {component} = 
			{c for (conn : connections (comp)) (c : backwards_reachable_components_via_connection(comp, conn))}
		NOTE: THIS CONTAINS A FORALL, OR WHAT ELSE IS THE FOR SYNTAX?

		backwards_reachable_components_via_connection(comp : component, conn : connection) : {component} = 
			if is_port_connection(conn) then 
				if destination_component(conn) = comp then 
					{source_component(conn)} 
				else 
					{} 
			else 
				{}
    NOTE: THIS CONTAINS A CONDITIONAL
				
		implementation_language_assurance(comp : component) <=
			** comp " implementation is appropriate for OS" **
			is_seL4_component(comp) => (has_property(comp, Filter_Properties::Component_Implementation) and property(comp, Filter_Properties::Component_Implementation) = "CakeML")
			
		-- checks that a component will run on seL4 by checking that the processors it is bound to have the seL4 OS property
		is_seL4_component(comp : component) : bool =
			let proc : {component} = {c for (c : component) | (is_processor(c) or is_virtual_processor(c)) and is_bound_to(comp, c)};
			(size(proc) > 0) and forall (p : proc) . (has_property(p, Filter_Properties::OS) and property(p, Filter_Properties::OS) = "seL4")
  NOTE: THIS CONTAINS A FORALL STATEMENT
	
	**};
*)

(*
		goal filter_added(comp_context : component, filter : component, conn : connection, msg_type : data) <=
			** "Filter " filter " is properly added to component " comp_context **
			strategy S3 : "Reason over architecture";
			filter_exists(filter, comp_context, conn) and filter_not_bypassed(filter, comp_context, msg_type) and filter_implemented(filter)
*)

Definition and_template : Resolute := R_And (R_Goal 0 []) (R_Goal 0 []).
Definition imp_template : Resolute := R_Imp (R_Goal 0 []) (R_Goal 0 []).

Notation "x R& y" := (R_And x y)
                     (at level 20, right associativity).

Notation "x R=> y" := (R_Imp x y)
                     (at level 20, right associativity).

Definition foo := R_Goal (0) [].

Definition and_temp2 : Resolute := foo R& foo.
Definition imp_temp2 : Resolute := foo R=> foo.                               

Definition filter : Arg := 0.
Definition comp_context : Arg := 1.
Definition conn : Arg := 2.
Definition msg_type : Arg := 3.
Definition filter_exists : TargetT := 0.
Definition filter_not_bypassed : TargetT := 1.
Definition filter_implemented : TargetT := 2.

(*
Definition ex1_filter_added : Resolute :=
  R_And (R_Goal filter_exists) (R_And (R_Goal filter_not_bypassed) (R_Goal filter_implemented)).

Definition ex2_filter_added : Resolute :=
  R_And 
  (R_Imp (R_And (R_Goal filter) (R_And (R_Goal comp_context) (R_Goal conn))) (R_Goal filter_exists))
   (R_And 
   (R_Imp (R_And (R_Goal filter) (R_And (R_Goal comp_context) (R_Goal msg_type))) (R_Goal filter_not_bypassed)) 
   (R_Imp (R_Goal filter) (R_Goal filter_implemented))).
*)

Definition bar : list Arg := [filter; comp_context; conn].

Definition filter_added : Resolute :=
(R_Goal (filter_exists) ([filter; comp_context; conn])) 
R& (R_Goal (filter_not_bypassed) ([filter; comp_context; msg_type])) 
R& (R_Goal (filter_implemented) ([filter])).

Definition copland_filter_added := res_to_copland test_model filter_added.

Compute copland_filter_added.

Example test_filter_added :
(
Reval [] (R_Goal (filter_exists) ([filter; comp_context; conn]))
) ->
(
Reval [] (R_Goal (filter_not_bypassed) ([filter; comp_context; msg_type]))
) ->
(
Reval [] (R_Goal (filter_implemented) ([filter]))
) -> 
Reval [] filter_added.
Proof.
intros. unfold filter_added. apply Reval_And_Intro.
- apply H.
- apply Reval_And_Intro.
  + apply H0.
  + apply H1.
Qed.

Example test_filter_added2 :
Reval 
[
  (R_Goal (filter_exists) ([filter; comp_context; conn]));
  (R_Goal (filter_not_bypassed) ([filter; comp_context; msg_type]));
  (R_Goal (filter_implemented) ([filter]))
] 
filter_added.
Proof.
intros. unfold filter_added. apply Reval_And_Intro.
- apply Reval_Take_One_Assumption. apply Reval_ID_Simple.
- apply Reval_Weaken_Assumptions. apply Reval_And_Intro.
  + apply Reval_Take_One_Assumption. apply Reval_ID_Simple. 
  + apply Reval_Weaken_Assumptions.
    apply Reval_Take_One_Assumption. apply Reval_ID_Simple.
Qed.

Example test_filter_added3 :
Reval 
[
  (R_Goal (filter_exists) ([filter; comp_context; conn]));
  (R_Goal (filter_not_bypassed) ([filter; comp_context; msg_type]));
  (R_Goal (filter_implemented) ([filter]))
] 
filter_added.
Proof.
intros. unfold filter_added. apply Reval_And_Intro.
- apply Reval_ID_List. simpl. auto.
- apply Reval_And_Intro.
  + apply Reval_ID_List. simpl. auto.
  + apply Reval_ID_List. simpl. auto.
Qed.

(* ====================================== *)
(* ASSORTED LEFTOVER CODE AND TESTS BELOW *)
(* ====================================== *)

    (*

  | R_Forall l pred => 
    (* forall x \in l, do pred l *)
    let list_tpols := map (fun x => res_to_copland M (pred x)) l in
    fold_left (fun x y => (bseq (NONE,NONE) (fst x) (fst y), fun e => andb ((snd x) e) ((snd y) e))) list_tpols (mtTerm, fun e => true)

  | R_Exists l pred => 
    (* exists x \in l, do pred l *)
    let list_tpols := map (fun x => res_to_copland M (pred x)) l in
    fold_left (fun x y => (bseq (NONE,NONE) (fst x) (fst y), fun e => andb ((snd x) e) ((snd y) e))) list_tpols (mtTerm, fun e => false)
  end.
  *)




(*
Definition targets := [1; 2; 3].

Definition ex_forall := 
R_Forall targets 
(fun target => R_Goal [target] (fun target => R_True)).



Definition is_more_than_zero (l: list Target_ID) : Resolute :=
  match l with
  | [O] => R_False
  | [S x] => R_True
  | _ => R_False
  end.

Definition is_bound (l : list Target_ID) : Resolute :=
  match l with
  | [process; processor] => R_True
  | _ => R_False 
  end.

*)

(*
		one_process() <=
			** "The model must contain at least one process bound to a processor" **
			let procs : {process} = {p for (p : process) | (exists(pr : processor) . is_bound_to(p, pr))};
			size(procs) > 0
*)

(*
(*
Definition processes := [1; 2; 3].
Definition processors := [1; 2; 3].

Definition appraiser := 0.

Definition is_bound_to := 0.
Definition is_more_than_zero := 1.

Definition one_process :=
R_And
(R_Forall processes
  (fun process =>
    (R_Exists processors
      (fun processor =>
          R_Goal nil (appraiser, is_bound_to, [process; processor])
      )
    )
  )
)
(R_Goal nil (appraiser, is_more_than_zero, [length processes])).

*)

*)

(*

Definition one_process := 
R_And 
(R_Forall processes 
  (fun process => 
    (R_Exists processors
      (fun processor =>
        R_Goal [process; processor] is_bound
      )
    )
  )
)
(R_Goal ([length processes]) is_more_than_zero).

*)

(*

(*
Definition copland_one_process := res_to_copland test_model one_process.

Compute copland_one_process.

Example test_one_process : Reval [] one_process.
Proof.
unfold one_process. apply Reval_And_R.
- apply Reval_Forall. 
  intros. apply Reval_Exists. 
  exists 1. intros H1. apply Reval_Goal. apply Reval_Assume_ASP_Succeeds. 
  apply Reval_R.
- simpl. apply Reval_Goal. apply Reval_Assume_ASP_Succeeds.
  simpl. apply Reval_R.
Qed. (* No admits needed! *)
*)
*)

(*
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
    + intros. specialize H with (t := conc m l).
    simpl in H. specialize H with (pol := fun e => In e (spec m l)).
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
*)

(*
(*
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


*)
*)
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
