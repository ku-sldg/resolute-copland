(* The Main interface for JSON that exports its sub-properties *)

Require Export JSON_Type JSON_Admits ResultT StructTactics.
Require Import List String Maps Stringifiable EqClass ErrorStringConstants.
Import ListNotations.

(* The JSONIFIABLE Class *)
Class Jsonifiable (A : Type) :=
  {
    to_JSON : A -> JSON;
    from_JSON : JSON -> ResultT A string;
    canonical_jsonification : forall (a : A), 
      from_JSON (to_JSON a) = resultC a
  }.

(* Global Instance Stringifiable_Jsonifiables {A : Type} `{Jsonifiable A} : Stringifiable A.
pose proof (Build_Stringifiable A (fun a => JSON_to_string (to_JSON a)) (fun a => match string_to_JSON a with | errC e => errC e | resultC js => from_JSON js end)).
intuition.
eapply X.
intuition.
rewrite canonical_serialization_json_string; 
rewrite canonical_jsonification; eauto.
Defined. *)

(* The JSONIFIABLE Class *)

Open Scope string_scope.

Definition JSON_get_Object (key : string) (js : JSON) : ResultT JSON string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_Object v => resultC v
          | _ => errC "JSON_get_Object: NOT AN OBJECT"
          end
      | None => errC "JSON_get_Object: KEY NOT FOUND"
      end
  end.

Fixpoint JSON_map_get_Object_rec_safe (key : string) (js_map : MapC string InnerJSON) : ResultT JSON string :=
  match js_map with
  | [] => errC ("NO OBJECT """ ++ key ++ """")
  | (key', val) :: js_map' =>
      if (eqb key key') 
      then (match val with
            | InJSON_Object v => resultC v
            | _ => errC "JSON_map_get_Object_rec_safe: NOT AN OBJECT"
            end)
      else JSON_map_get_Object_rec_safe key js_map'
  end.

Definition JSON_get_Array (key : string) (js : JSON) : ResultT (list InnerJSON) string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_Array v => resultC v
          | _ => errC errStr_json_get_array_not_an_array
          end
      | None => errC errStr_json_get_array_key_not_found
      end
  end.

Definition JSON_get_string (key : string) (js : JSON) : ResultT string string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_String v => resultC v
          | _ => errC errStr_json_get_string_not_a_string
          end
      | None => errC errStr_json_get_string_key_not_found
      end
  end.

Definition JSON_get_bool (key : string) (js : JSON) : ResultT bool string :=
  match js with
  | JSON_Object m => 
      match map_get m key with
      | Some ijs => 
          match ijs with
          | InJSON_Boolean v => resultC v
          | _ => errC errStr_json_get_bool_not_a_bool
          end
      | None => errC errStr_json_get_bool_key_not_found
      end
  end.

(* Lemma canonical_serialization_string : forall (js : JSON) (a : string), 
  JSON_String a = js <-> (resultC (JSON_to_string js) = @resultC _ string a).
Proof.
  setoid_rewrite canonical_serialization_json_string; intuition; eauto.
  - rewrite H; eauto. 
  - inversion H; eauto. 
Qed. *)

(* The Pair JSONIFIABLE Class *)
Definition pair_to_JSON_Array {A B : Type} `{Stringifiable A, Stringifiable B} (v : (A * B)) : InnerJSON :=
  InJSON_Array [InJSON_String (to_string (fst v)); InJSON_String (to_string (snd v))].

Definition InnerJSON_to_pair {A B : Type} `{Stringifiable A, Stringifiable B} (js : InnerJSON) : ResultT (A * B) string :=
  match js with
  | InJSON_Array [InJSON_String a; InJSON_String b] =>
      match (from_string a), (from_string b) with
      | resultC a, resultC b => resultC (a, b)
      | _, _ => errC errStr_json_to_pair
      end
  | _ => errC errStr_json_to_pair
  end.

Definition map_serial_serial_to_JSON {A B : Type} `{Stringifiable A, Stringifiable B, EqClass A} (m : MapC A B) : JSON :=
  JSON_Object (
    map (fun '(k, v) => (to_string k, InJSON_String (to_string v))) m).

Definition map_serial_serial_from_JSON {A B : Type} `{Stringifiable A, Stringifiable B, EqClass A} (js : JSON) : ResultT (MapC A B) string :=
  match js with
  | JSON_Object m => 
      result_map 
        (fun '(k, v) => 
            match v with
            | InJSON_String v' =>
              match (from_string k), (from_string v') with
              | resultC k', resultC v' => resultC (k', v')
              | _, _ => errC "Error in map_serial_serial_from_JSON"
              end
            | _ => errC "Error in map_serial_serial_from_JSON"
            end) m
  end.

Lemma canonical_jsonification_map_serial_serial : forall {A B} `{Stringifiable A, Stringifiable B, EqClass A} (m : MapC A B),
  map_serial_serial_from_JSON (map_serial_serial_to_JSON m) = resultC m.
Proof.
  intuition.
  induction m; simpl in *; eauto.
  repeat (try break_match; 
    subst; simpl in *; 
    try find_rewrite; 
    try find_injection; try congruence);
  repeat rewrite canonical_stringification in *;
  try congruence;
  repeat find_injection; eauto.
Qed.

Global Instance jsonifiable_map_serial_serial (A B : Type) `{Stringifiable A, EqClass A, Stringifiable B} : Jsonifiable (MapC A B) :=
  {
    to_JSON   := map_serial_serial_to_JSON;
    from_JSON := map_serial_serial_from_JSON;
    canonical_jsonification := canonical_jsonification_map_serial_serial;
  }.

Global Instance jsonifiable_map_serial_json (A B : Type) `{Stringifiable A, EqClass A, Jsonifiable B} : Jsonifiable (MapC A B). 
eapply Build_Jsonifiable with (
  to_JSON := (fun m => JSON_Object (
                      map (fun '(k, v) => 
                            (to_string k, InJSON_Object (to_JSON v))
                          ) m))) 
  (from_JSON := (fun js =>   
                    match js with
                    | JSON_Object m => 
                        result_map 
                          (fun '(k, v) => 
                              match v with
                              | InJSON_Object v' =>
                                match (from_string k), (from_JSON v') with
                                | resultC k', resultC v' => resultC (k', v')
                                | _, _ => errC "Error in jsonifiable_map_serial_json"
                                end
                              | _ => errC errStr_json_to_map
                              end) m
                    end)).
intuition; induction a; simpl in *; intuition; eauto;
repeat (try break_match; simpl in *; subst; eauto; try congruence);
try rewrite canonical_jsonification in *; 
try rewrite canonical_stringification in *; 
repeat find_injection; simpl in *; 
try find_rewrite; eauto; try congruence.
Defined.

Close Scope string_scope.

(* Definition JSON_to_string_map {B : Type} `{Jsonifiable B} (js : JSON) 
    : ResultT (MapC string B) string :=

Definition JSON_to_string_string_map {B : Type} `{Stringifiable B} (js : JSON) 
    : ResultT (MapC string B) string :=

Global Instance jsonifiable_string_map (A : Type) `{Jsonifiable A} : Jsonifiable (MapC string A) :=
  {
    to_JSON := string_map_to_JSON;
    from_JSON := JSON_to_string_map
  }. *)

(* Global Instance jsonifiable_id_map (A : Type) `{Jsonifiable A} : Jsonifiable (MapC ID_Type A) :=
  {
    to_JSON := (fun m => string_map_to_JSON (id_map_to_string_map m));
    from_JSON := (fun js => 
                    match JSON_to_string_map js with
                    | errC e => errC e
                    | resultC m => string_map_to_id_map m
                    end)
  }.

Fixpoint id_B_map_to_string_map {B : Type} `{Stringifiable ID_Type, Stringifiable B} (m : MapC ID_Type B) : MapC string string :=
  match m with
  | [] => []
  | (k, v) :: m' => (to_string k, to_string v) :: (id_B_map_to_string_map m')
  end.

Fixpoint string_map_to_id_B_map {B : Type} `{Stringifiable ID_Type, Stringifiable B} (m : MapC string string) : ResultT (MapC ID_Type B) string :=
  match m with
  | [] => resultC []
  | (k, v) :: m' => 
    match (from_string k), (from_string v) with
    | resultC k', resultC v' => 
      match (string_map_to_id_B_map m') with
      | errC e => errC e
      | resultC m'' => resultC ((k', v') :: m'')
      end
    | _, _ => errC "Error in string_map_to_id_B_map"%string
    end
  end.

Global Instance jsonifiable_id_map_Stringifiables (A : Type) `{Stringifiable A} : Jsonifiable (MapC ID_Type A) :=
  {
    to_JSON := (fun m => string_string_map_to_JSON (id_B_map_to_string_map m));
    from_JSON := (fun js => 
                    match JSON_to_string_string_map js with
                    | errC e => errC e
                    | resultC m => string_map_to_id_B_map m
                    end)
  }. *)

Fixpoint map_flatten {A B C : Type} `{EqClass A, EqClass B} 
    (m : MapC (A * B) C) : list (A * B * C) :=
  match m with
  | [] => []
  | ((k1, k2), v) :: m' => (k1,k2,v) :: map_flatten m'
  end.

Fixpoint result_map_pairs {A B C : Type} `{EqClass A, EqClass B} (f : InnerJSON -> ResultT ((A * B) * C) string) (l : list InnerJSON)
    : ResultT (MapC (A * B) C) string :=
  match l with
  | [] => resultC []
  | h :: t => 
      match f h with
      | errC e => errC e
      | resultC ((k1, k2), v) => 
          match result_map_pairs f t with
          | errC e => errC e
          | resultC m' => resultC (((k1, k2), v) :: m')
          end
      end
  end.

Definition map_pair_to_InnerJSON_string {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Stringifiable C} (m : MapC (A * B) C) : list InnerJSON :=
  List.map (fun '(k1, k2, v) => InJSON_Array [InJSON_String (to_string k1); InJSON_String (to_string k2); InJSON_String (to_string v)]) (map_flatten m).

Definition InnerJson_string_to_map_pair {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Stringifiable C} (js : list InnerJSON) 
    : ResultT (MapC (A * B) C) string :=
  result_map_pairs 
    (fun js' => 
        match js' with
        | InJSON_Array [InJSON_String k1; InJSON_String k2; InJSON_String v] =>
          match (from_string k1), (from_string k2), (from_string v) with
          | resultC k1, resultC k2, resultC v => resultC ((k1, k2), v)
          | _, _, _ => errC errStr_json_to_map
          end
        | _ => errC errStr_json_to_map
        end) js.

(* Definition map_pair_to_InnerJSON {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Jsonifiable C} (m : MapC (A * B) C) : list InnerJSON :=
  List.map (fun '(k1, k2, v) => InJSON_Array [InJSON_String (to_string k1); InJSON_String (to_string k2); InJSON_Object (to_JSON v)]) (map_flatten m).

Definition InnerJson_to_map_pair {A B C : Type} `{Stringifiable A, EqClass A, EqClass B, Stringifiable B, Jsonifiable C} (js : list InnerJSON) 
    : ResultT (MapC (A * B) C) string :=
  result_map_pairs 
    (fun js' => 
        match js' with
        | InJSON_Array [InJSON_String k1; InJSON_String k2; InJSON_Object v] =>
          match (from_string k1), (from_string k2), (from_JSON v) with
          | resultC k1, resultC k2, resultC v => resultC ((k1, k2), v)
          | _, _, _ => errC errStr_json_to_map
          end
        | _ => errC errStr_json_to_map
        end) js. *)