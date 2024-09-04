Inductive testT := testC.

Require Import StructTactics.
Require Import String List Lia.
Import ListNotations.

Definition Forall' {A : Type} (P : A -> Prop) : list A -> Prop :=
  fix F l :=
    match l with
    | nil => True
    | x :: l' => P x /\ F l'
    end.

Theorem Forall'_spec : forall A P (l : list A),
  Forall' P l <->
  (forall a, In a l -> P a).
Proof.
  induction l; ff.
Qed.

Definition Exists' {A : Type} (P : A -> Prop) : list A -> Prop :=
  fix F l :=
    match l with
    | nil => False
    | x :: l' => P x \/ F l'
    end.

Theorem Exists'_spec : forall A P (l : list A),
  Exists' P l <->
  (exists a, In a l /\ P a).
Proof.
  induction l; ff.
  - rewrite IHl in H0; ff. 
  - assert (exists x, In x l /\ P x) by ff.
    rewrite <- IHl in H; ff.
Qed.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).
Arguments vnil {A}.
Arguments vcons {A} _ {n} _.
Notation "[||]" := vnil (at level 150).
Notation "[| x ; .. ; y |]" := (vcons x .. (vcons y vnil) ..) (at level 160).
Notation "x |:: v" := (vcons x v) (at level 60, right associativity).

Example vec_ex1 : vec nat 3 := [| 1 ; 2 ; 3 |].
Example vec_ex2 : vec nat 3 := 1 |:: 2 |:: 3 |:: vnil.
Example vec_ex_eq1 : vec_ex1 = vec_ex2 := eq_refl.

Module Type FOL_Language.
  (* NOTE: Constants are considered 0 argument Functions! *)
  Parameter Preds : list (string * nat).

  Parameter Funcs : list (string * nat).

  Inductive Logicals :=
  | Log_neg 
  | Log_conj
  | Log_disj
  | Log_cond
  | Log_univ
  | Log_exists
  | Log_bot
  | Log_eq
  | Log_var : string -> Logicals.

  Inductive Symbols :=
  | Sym_pred : { x | In x Preds } -> list Symbols -> Symbols
  | Sym_func : { x | In x Funcs } -> list Symbols -> Symbols
  | Sym_log : Logicals -> Symbols
  | Sym_comma.

End FOL_Language.

Module FOL.

  Declare Module L : FOL_Language.

  Unset Positivity Checking.

  Inductive Term :=
  | T_var : string -> Term
  | T_func : { x | In (fst x) L.Funcs /\ @length Term (snd x) = snd (fst x) } -> Term.

  Print map.

  Definition fancy_map {A : Type} {P : A -> Prop} (fn : A -> A) (projFn : { x | P x } -> list A) : { x | P x } -> { x | P x }.
    refine (fun l =>
      match l with
      | exist _ (p', nil) PV => exist _ (p', nil) PV
      | exist _ (p', (x :: l)) PV => exist _ (p', (fn x :: map fn l)) _
      end).
    simpl in *; intuition;
    erewrite map_length; ff.
  Defined.

  Fixpoint closed_term (t : Term) :=
    match t with
    | T_var _ => False
    | T_func l => Forall' closed_term (snd (proj1_sig l))
    end.

  Inductive Formula :=
  | F_bot : Formula
  | F_pred : { x | In (fst x) L.Preds /\ @length Term (snd x) = snd (fst x) } -> Formula
  | F_eq : Term -> Term -> Formula
  | F_not : Formula -> Formula
  | F_and : Formula -> Formula -> Formula
  | F_or : Formula -> Formula -> Formula
  | F_impl : Formula -> Formula -> Formula
  | F_forall : string -> Formula -> Formula
  | F_exists : string -> Formula -> Formula.

  Definition syntactic_eq (s1 s2 : list L.Symbols) :=
    s1 = s2.

  Fixpoint proper_subformula (f : Formula) : list Formula :=
    match f with
    | F_bot => nil
    | F_pred l => nil
    | F_eq _ _ => nil
    | F_not f' => f' :: proper_subformula f'
    | F_and f1 f2 => f1 :: f2 :: proper_subformula f1 ++ proper_subformula f2
    | F_or f1 f2 => f1 :: f2 :: proper_subformula f1 ++ proper_subformula f2
    | F_impl f1 f2 => f1 :: f2 :: proper_subformula f1 ++ proper_subformula f2
    | F_forall _ f' => f' :: proper_subformula f'
    | F_exists _ f' => f' :: proper_subformula f'
    end.

  Definition subformula (f : Formula) : list Formula :=
    f :: proper_subformula f.

  Fixpoint vars_term (t : Term) : list string :=
    match t with
    | T_var x => [x]
    | T_func l => flat_map vars_term (snd (proj1_sig l))
    end.

  Fixpoint free_vars_term (t : Term) : list string :=
    match t with
    | T_var x => [x]
    | T_func l => flat_map free_vars_term (snd (proj1_sig l))
    end.

  Fixpoint vars_formula (f : Formula) : list string :=
    match f with
    | F_bot => nil
    | F_pred l => flat_map vars_term (snd (proj1_sig l))
    | F_eq t1 t2 => vars_term t1 ++ vars_term t2
    | F_not f' => vars_formula f'
    | F_and f1 f2 => vars_formula f1 ++ vars_formula f2
    | F_or f1 f2 => vars_formula f1 ++ vars_formula f2
    | F_impl f1 f2 => vars_formula f1 ++ vars_formula f2
    | F_forall x f' => vars_formula f'
    | F_exists x f' => vars_formula f'
    end.

  Fixpoint free_vars_formula (f : Formula) : list string :=
    match f with
    | F_bot => nil
    | F_pred l => flat_map free_vars_term (snd (proj1_sig l))
    | F_eq t1 t2 => free_vars_term t1 ++ free_vars_term t2
    | F_not f' => free_vars_formula f'
    | F_and f1 f2 => free_vars_formula f1 ++ free_vars_formula f2
    | F_or f1 f2 => free_vars_formula f1 ++ free_vars_formula f2
    | F_impl f1 f2 => free_vars_formula f1 ++ free_vars_formula f2
    | F_forall x f' => remove string_dec x (free_vars_formula f')
    | F_exists x f' => remove string_dec x (free_vars_formula f')
    end.

  Definition var_bound_term (t : Term) : list string :=
    let vars := vars_term t in
    let free_vars := free_vars_term t in
    filter (fun x => if In_dec string_dec x free_vars then false else true) vars.

  Definition var_bound_formula (f : Formula) : list string :=
    let vars := vars_formula f in
    let free_vars := free_vars_formula f in
    filter (fun x => if In_dec string_dec x free_vars then false else true) vars.

  Definition sentence (f : Formula) :=
    free_vars_formula f = nil.

  Definition subst_term (x : string) (t' : Term) : Term -> Term :=
    fix subst_term t :=
      match t with
      | T_var x' => if string_dec x x' then t' else t
      | T_func l => T_func (fancy_map subst_term l)
      end.
  destruct l, x0; simpl in *.
  set (l' := map subst_term l).
  pose proof (@exist).
  assert (In p L.Funcs /\ length l' = (snd p)). {
    intuition.
    subst l'.
    rewrite map_length.
    eauto.
  }
  eapply (T_func (@exist _ (fun x0 => In (fst x0) L.Funcs /\ length (snd x0) = snd (fst x0)) (p, l') H)). 
  Defined.
  eapply H0.



  destruct t.
  - eapply (if string_dec x s then t' else T_var s). 
  - destruct s, x0; simpl in *.
    set (l' := map )
    pose 
    match t with
    | T_var x' => if string_dec x x' then t' else t
    | T_func l => T_func (exist _ (fst (proj1_sig l), map (subst_term x t') (snd (proj1_sig l)) _) _)
    end.

  Definition subst_term (x : string) (t' : Term) : Term -> Term :=
    fix subst_term t :=
      match t with
      | T_var x' => if string_dec x x' then t' else t
      | T_func l => T_func (map subst_term (snd (proj1_sig l)))
      end.

  Definition subst_formula (x : string) (t' : Term) : Formula -> Formula :=
    fix subst_formula f :=
      match f with
      | F_bot => F_bot
      | F_pred p l => F_pred p (map (subst_term x t') l)
      | F_eq t1 t2 => F_eq (subst_term x t' t1) (subst_term x t' t2)
      | F_not f1 => F_not (subst_formula f1)
      | F_and f1 f2 => F_and (subst_formula f1) (subst_formula f2)
      | F_or f1 f2 => F_or (subst_formula f1) (subst_formula f2)
      | F_impl f1 f2 => F_impl (subst_formula f1) (subst_formula f2)
      | F_forall x' f1 => if string_dec x x' then F_forall x' f1 else F_forall x' (subst_formula f1)
      | F_exists x' f1 => if string_dec x x' then F_exists x' f1 else F_exists x' (subst_formula f1)
      end.

  Record Model := {
    Domain      : Type;
    ConstInterp : string -> Domain;
    FuncInterp  : { x | In x L.Funcs } -> list Domain -> Domain;
    Relations : string -> list Domain -> Prop
  }.

Inductive Term :=
| Var : string -> Term