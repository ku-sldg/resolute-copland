Require Export String ResultT.
Open Scope string_scope.

Class Stringifiable (A : Type) :=
  {
    to_string : A -> string;
    from_string : string -> ResultT A string;
    canonical_stringification : forall a, 
      from_string (to_string a) = resultC a;
  }.

Global Instance Stringifiable_string : Stringifiable string :=
  {
    to_string := fun s => s;
    from_string := fun s => resultC s;
    canonical_stringification := fun s => eq_refl;
  }.

Global Instance Stringifiable_bool : Stringifiable bool :=
  {
    to_string := fun b => if b then "true" else "false";
    from_string := fun s => 
                     match s with
                     | "true" => resultC true
                     | "false" => resultC false
                     | _ => errC "Not a boolean"
                     end;
    canonical_stringification := fun b =>
                                   match b with
                                   | true => eq_refl
                                   | false => eq_refl
                                   end;
  }.

Close Scope string_scope.
