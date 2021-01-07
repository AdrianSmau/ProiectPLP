Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(* ~~~ SINTAXA ~~~*)

(*--------------- TIPURI DE DATE + MEM ---------------*)

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem.

Scheme Equality for Mem.

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Scheme Equality for ErrorNat.

Coercion num: nat >-> ErrorNat.

Check num 3.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Scheme Equality for ErrorBool.

Coercion boolean: bool >-> ErrorBool.

Check boolean true.

Inductive ErrorString :=
  | error_string : ErrorString
  | Sstring : string -> ErrorString.

Coercion Sstring: string >-> ErrorString.

Check Sstring "PLP".

Inductive ErrorPtr :=
  | error_ptr : ErrorPtr
  | ptr : Mem -> ErrorPtr.

Check ptr (offset 4).

Inductive ErrorRef :=
  | error_ref : ErrorRef
  | ref : Mem -> ErrorRef.

Check ref mem_default.

(*--------------- END TIPURI DE DATE + MEM ---------------*)

(*Cele 2 tipuri de date, semantic, vor prelua offset-ul variabilelor asignate*)

(*--------------- STRUCT-URI ---------------*)

Inductive FieldValues :=
| nat_value : ErrorNat -> FieldValues
| bool_value : ErrorBool -> FieldValues
| ptr_value : ErrorPtr -> FieldValues
| ref_value : ErrorRef -> FieldValues
| string_value : ErrorString -> FieldValues
| error_struct : FieldValues.

Coercion nat_value: ErrorNat >-> FieldValues.
Coercion bool_value: ErrorBool >-> FieldValues.
Coercion ptr_value: ErrorPtr >-> FieldValues.
Coercion ref_value: ErrorRef >-> FieldValues.
Coercion string_value: ErrorString >-> FieldValues.

Inductive Field :=
| field : string -> FieldValues -> Field.

Check (field "field1" "x").
Check (field "field1" (ptr (offset 5))).

Inductive Struct :=
| struct: (list Field) -> Struct.

Check (struct ((field "camp1" 10) :: (field "camp2" "text") :: nil)).

Notation "'[[' L ']]'" := (struct L) (at level 95).

Check ([[(field "field1" 2) :: (field "field2" "txt") :: nil]]).

(*--------------- END STRUCT-URI ---------------*)

Inductive AExp :=
  | avar: string -> AExp
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp
  | adiv: AExp -> AExp -> AExp
  | amod: AExp -> AExp -> AExp.

Coercion avar: string >-> AExp.
Coercion anum: ErrorNat >-> AExp.

Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).

Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bbool : ErrorBool -> BExp
  | bvar: string -> BExp
  | blt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp.

Coercion bvar: string >-> BExp.

Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).

Inductive SExp :=
  | sstr : ErrorString -> SExp
  | svar : string -> SExp
  | scat : SExp -> SExp -> SExp
  | ssub : SExp -> AExp -> AExp -> SExp.

Coercion svar: string >-> SExp.

Notation "A +s B" := (scat A B) (at level 54,left associativity).
Notation "'substr' A B C" := (ssub A B C) (at level 55).
(* PAIR PENTRU SWITCH *)

Inductive Pair (T1 T2 : Type) :=
  | pair (t1 : T1) (t2 : T2).

Inductive Stmt :=
| int_decl: string -> Stmt
| boolean_decl: string -> Stmt
| ptr_decl: string -> Stmt
| str_decl : string -> Stmt
| structure_decl : string -> Stmt
| function_decl : string -> Stmt
| assgn_ptr: string -> string -> Stmt
| assgn_ref: string -> string -> Stmt
| assgn_int : string -> AExp -> Stmt
| assgn_bool : string -> BExp -> Stmt
| assgn_string : string -> SExp -> Stmt
| void_func : string -> (list string) -> Stmt -> Stmt
| int_func : string -> string -> string -> (list string) -> Stmt -> Stmt
(*int_func <nume_functie> <variabila in care vom pune valoarea - trebuie sa fie nat_decl> <variabila din configuratia creata de functia a carei valoare o vom returna> <lista de parametri> <ce face functia>*)
| bool_func : string -> string -> string -> (list string) -> Stmt -> Stmt
(*bool_func <nume_functie> <variabila in care vom pune valoarea - trebuie sa fie bool_decl> <variabila din configuratia creata de functia a carei valoare o vom returna> <lista de parametri> <ce face functia>*)
| assgn_struct : string -> Struct -> Stmt
| setStructField : Struct -> string -> string -> FieldValues -> Stmt
| getStruct : Struct -> string -> Stmt
| getPtrVal : ErrorPtr -> string -> Stmt
| getRefVal : ErrorRef -> string -> Stmt
| setPtrVal : ErrorPtr -> string -> Stmt
| break : Stmt
| switch_int : string -> list (Pair ErrorNat Stmt) -> Stmt
| switch_bool : string -> list (Pair ErrorBool Stmt) -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

(*Un pointer poate fi declarat inainte de a fi initializat, insa o referinta nu*)

Notation "X :n= A" := (assgn_int X A) (at level 90).
Notation "X :b= A" := (assgn_bool X A) (at level 90).
Notation "X :p= A" := (assgn_ptr X A) (at level 90).
Notation "X :r= A" := (assgn_ref X A) (at level 90).
Notation "X :s= A" := (assgn_string X A) (at level 90).
Notation "X :struct= A" := (assgn_struct X A) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'If' B 'Then' S1 'Else' S2 'End'" := (ifthenelse B S1 S2) (at level 97).
Notation "'IFF' B 'THENN' S 'ENDD'" := (ifthen B S) (at level 97).
Notation "'While' B 'Do' S 'Done'" := (while B S) (at level 98).
Notation "'FOR' A B C 'DO' S 'DONE'" := (forr A B C S) (at level 98).

(* --------------- RESULT ---------------*)

Inductive Result :=
  | undecl : Result
  | err_assign : Result
  | nat_decl : Result
  | bool_decl : Result
  | func_decl : Result
  | pointer_decl : Result
  | string_decl : Result
  | struct_decl : Result
  | nat_val : ErrorNat -> Result
  | bool_val : ErrorBool -> Result
  | pointer_val : ErrorPtr -> Result
  | ref_val : ErrorRef -> Result
  | string_val : ErrorString -> Result
  | struct_val : Struct -> Result
  | func_val : Stmt -> Result.

Coercion nat_val: ErrorNat >-> Result.
Coercion bool_val: ErrorBool >-> Result.
Coercion pointer_val: ErrorPtr >-> Result.
Coercion ref_val: ErrorRef >-> Result.
Coercion string_val: ErrorString >-> Result.
Coercion struct_val : Struct >-> Result.

Definition check_eq_over_types (t1 : Result)(t2 : Result) : bool :=
  match t1 with
  | err_assign => match t2 with 
                   | err_assign => true
                   | _ => false
                   end
  | undecl => match t2 with 
                   | undecl => true
                   | _ => false
                   end
  | nat_decl => match t2 with 
                | nat_decl => true
                | _ => false
                end
  | struct_decl => match t2 with 
                | struct_decl => true
                | _ => false
                end
  | bool_decl => match t2 with 
                   | bool_decl => true
                   | _ => false
                   end
  | func_decl => match t2 with 
                   | func_decl => true
                   | _ => false
                   end
  | string_decl => match t2 with 
                   | string_decl => true
                   | _ => false
                   end
  | pointer_decl => match t2 with 
                   | pointer_decl => true
                   | _ => false
                   end
  | nat_val a => match t2 with 
                    | nat_val b => true
                    | _ => false
                    end
  | bool_val a => match t2 with 
                    | bool_val b => true
                    | _ => false
                    end
  | pointer_val a => match t2 with 
                    | pointer_val b => true
                    | _ => false
                    end
  | ref_val a => match t2 with 
                    | ref_val b => true
                    | _ => false
                    end
  | func_val a => match t2 with
                | func_val b => true
                | _ => false
                end
  | struct_val a => match t2 with
                | struct_val b => true
                | _ => false
                end
  | string_val a => match t2 with
                | string_val b => true
                | _ => false
                end
  end.

(* --------------- END RESULT ---------------*)
(* --------------- MEMLAYER (GLOBAL + BLANK) + ENV (GLOBAL + BLANK) + STACK(OF ENV) + CONFIG ---------------*)

Definition Env := string -> Mem.

Definition MemLayer := Mem -> Result.

Definition Stack := list Env.

Inductive Config :=
  | config : nat -> Env -> MemLayer -> Stack -> Config.

Definition update_env (env: Env) (x: string) (n: Mem) : Env :=
  fun y =>
      if (andb (string_beq x y ) (Mem_beq (env y) mem_default))
      then
        n
      else
        (env y).

Definition env_global : Env :=
  fun s =>
    if(string_beq s "x")
    then (offset 1)
    else if(string_beq s "y") then (offset 2)
      else mem_default.

Definition env_blank : Env :=
  fun s => mem_default.

Compute (env_global "z").

Compute (update_env env_global "z" (offset 3)) "z".

Compute (update_env env_global "x" (offset 3)) "x".

Definition update_mem (mem : MemLayer) (env : Env) (x : string) (type : Mem) (v : Result) : MemLayer :=
  fun y =>
    if (Mem_beq ((update_env env x type) x) y) then
      match v with
            | nat_decl => if(check_eq_over_types (mem type) undecl) then v else err_assign
            | bool_decl => if(check_eq_over_types (mem type) undecl) then v else err_assign
            | func_decl => if(check_eq_over_types (mem type) undecl) then v else err_assign
            | pointer_decl => if(check_eq_over_types (mem type) undecl) then v else err_assign
            | struct_decl => if(check_eq_over_types (mem type) undecl) then v else err_assign
            | string_decl => if(check_eq_over_types (mem type) undecl) then v else err_assign
            | nat_val a => match (mem type) with
                            | nat_decl => v
                            | nat_val b => v
                            | _ => err_assign
                           end
            | ref_val a => match (mem type) with
                            | undecl => v
                            | _ => err_assign
                           end
            | bool_val a => match (mem type) with
                            | bool_decl => v
                            | bool_val b => v
                            | _ => err_assign
                           end
            | func_val a => match (mem type) with
                            | func_decl => v
                            | func_val b => v
                            | _ => err_assign
                           end
            | struct_val a => match (mem type) with
                            | struct_decl => v
                            | struct_val b => v
                            | _ => err_assign
                           end
            | pointer_val a => match (mem type) with
                            | pointer_decl => v
                            | pointer_val b => v
                            | _ => err_assign
                           end
            | string_val a => match (mem type) with
                            | string_decl => v
                            | string_val b => v
                            | _ => err_assign
                           end
            | undecl => err_assign
            | err_assign => v
          end
    else
      (mem y).

Definition mem_global : MemLayer :=
  fun s =>
    if(Mem_beq s (offset 1)) then (nat_decl)
    else if (Mem_beq s (offset 2)) then (bool_decl)
      else undecl.
Definition mem_blank : MemLayer :=
  fun s => undecl.

Compute (mem_global (env_global "x")).
Compute (mem_global (env_global "y")).
Compute (mem_global (env_global "z")).
Compute (update_mem mem_global env_global "x" (offset 1) (nat_val 3)) (offset 1).
Compute (update_mem mem_global env_global "y" (offset 2) (bool_val true)) (offset 2).
Compute (update_mem (update_mem mem_global env_global "z" (offset 3) bool_decl) env_global "z" (offset 3) (bool_val true)) (offset 3).

Definition update_conf (s : string) (conf : Config) (r : Result) : Config :=
match conf with
  | config nbr env mem stack =>
      match r with
        | func_val a => (config (nbr) env (update_mem mem env s (env s) r) (env :: stack))
        | nat_val a => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | bool_val a => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | string_val a => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | struct_val a => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | pointer_val a => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | ref_val a => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | err_assign => (config (nbr) env (update_mem mem env s (env s) r) stack)
        | _ => (config (nbr+1) (update_env env s (offset (nbr+1))) (update_mem mem (update_env env s (offset (nbr+1))) s (offset (nbr+1)) r) stack)
    end
      end.
Definition stack : Stack := nil.
Definition conf_global : Config := (config 2 env_global mem_global stack).
Compute (update_conf "z" conf_global undecl).

Definition getConfigElementOffset (conf : Config) (s : string) :=
match conf with
| config nat env memlayer stack => (env s)
end.

Compute (getConfigElementOffset conf_global "x").
Compute (getConfigElementOffset conf_global "y").
Compute (getConfigElementOffset conf_global "z").

Definition getConfigMemzoneResult (conf : Config) (mem : Mem) :=
match conf with
| config nat env memlayer stack => (memlayer mem)
end.

Compute (getConfigMemzoneResult conf_global (offset 1)).
Compute (getConfigMemzoneResult conf_global (offset 2)).
Compute (getConfigMemzoneResult conf_global (offset 3)).
Compute (getConfigMemzoneResult conf_global mem_default).

Definition getConfigLastMemzone (conf : Config) :=
match conf with
| config nat env memlayer stack => nat
end.

Compute (getConfigLastMemzone conf_global).

Definition getConfigLastEnvStack (conf : Config) : Env :=
match conf with
| config nat env memlayer stack => match stack with
                                  | nil => env_global
                                  | (c :: stack') => c
                                  end
end.

Compute (getConfigElementOffset (update_conf "z" conf_global func_decl) "z").
Compute (getConfigElementOffset (update_conf "z" (update_conf "z" conf_global func_decl) (func_val (int_decl "k"))) "z").
Compute (getConfigMemzoneResult (update_conf "z" (update_conf "z" conf_global nat_decl) (nat_val 6)) (offset 3)).
Compute (getConfigMemzoneResult (update_conf "z" conf_global func_decl) (offset 3)).
Compute (getConfigLastMemzone (update_conf "z" conf_global func_decl)).
Compute getConfigMemzoneResult (update_conf "z" (update_conf "z" conf_global func_decl) (func_val (int_decl "k"))) (offset 3).

(* --------------- END MEMLAYER (GLOBAL + BLANK) + ENV (GLOBAL + BLANK) + STACK(OF ENV) + CONFIG ---------------*)



(* ~~~ END SINTAXA ~~~*)
(* ~~~ SEMANTICA ~~~*)



(*--------------- SEMANTICA AEXP ---------------*)

Definition plus (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.
Definition minus (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => if Nat.ltb v1 v2
                        then error_nat
                        else num (v1 - v2)
    end.
Definition multiply (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.
Definition divide (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.
Definition modulo (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Config -> ErrorNat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=> match (getConfigMemzoneResult sigma (getConfigElementOffset sigma v)) with
                                                | nat_val x => x
                                                | _ => error_nat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = plus (i1) (i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = multiply (i1) (i2) ->
    a1 *' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = divide (i1) (i2)->
    a1 /' a2 =[sigma]=> n
| modulus : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = modulo (i1) (i2)->
    a1 %' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = minus (i1) (i2)->
    a1 -' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Example ex1 : "x" =[ conf_global ]=> error_nat.
Proof.
  eapply var.
Qed.

Example ex2 : "x" *' "x" =[ update_conf "x" conf_global (nat_val 10) ]=> 100.
Proof.
  eapply times; eauto.
  eapply var.
  eapply var.
  simpl;reflexivity.
Qed.
(*--------------- END SEMANTICA AEXP ---------------*)
(*--------------- SEMANTICA BEXP ---------------*)

Definition and (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition not (n : ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition lessthan (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.leb v1 v2)
    end.

Definition or (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Reserved Notation "B ={ S }=> B'" (at level 70).
Inductive beval : BExp -> Config -> ErrorBool -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> error_bool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=> match (getConfigMemzoneResult sigma (getConfigElementOffset sigma v)) with
                                                | bool_val x => x
                                                | _ => error_bool
                                              end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (lessthan i1 i2) ->
    a1 <' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (not i1) ->
    !'a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (and i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (or i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
where "B ={ S }=> B'" := (beval B S B').

Example ex3 : "y" ={ conf_global }=> (error_bool).
Proof.
  eapply b_var.
Qed.

Example ex4: "x" <' 11 ={ update_conf "x" conf_global (nat_val 9) }=> true.
Proof.
  eapply b_lessthan.
  - eapply var.
  - eapply const.
  - simpl. reflexivity.
Qed.

Example ex5 : band bfalse "y" ={ update_conf "y" conf_global (bool_val true)}=> false.
Proof.
  eapply b_and.
  eapply b_false.
  eapply b_var.
  simpl;reflexivity.
Qed.

(*--------------- END SEMANTICA BEXP ---------------*)
(*--------------- SEMANTICA SEXP ---------------*)

Definition cat (n1 n2 : ErrorString) : ErrorString :=
  match n1, n2 with
    | error_string, _ => error_string
    | _, error_string => error_string
    | Sstring v1, Sstring v2 => Sstring (v1 ++ v2)
  end.

Definition subb (n : ErrorString) (a1 a2 : ErrorNat) : ErrorString :=
  match n with
    | error_string => error_string
    | Sstring v => match a1,a2 with
                     | error_nat, _ => error_string
                     | _, error_nat => error_string
                     | num n1, num n2 => Sstring (substring n1 n2 v)
                    end
  end.

Reserved Notation "S =(( X ))=> S'" (at level 72).
Inductive seval : SExp -> Config -> ErrorString -> Prop :=
| s_const : forall n sigma, (sstr n) =(( sigma ))=> n
| s_var : forall v sigma, svar v =(( sigma ))=> match (getConfigMemzoneResult sigma (getConfigElementOffset sigma v)) with
                                                | string_val x => x
                                                | _ => error_string
                                              end
| concat : forall a1 a2 i1 i2 sigma s,
    a1 =(( sigma ))=> i1 ->
    a2 =(( sigma ))=> i2 ->
    s = (cat i1 i2) ->
    a1 +s a2 =(( sigma ))=> s
| substring : forall a1 i1 n1 i2 n2 i3 sigma s,
   a1 =(( sigma ))=> i1 ->
   n1 =[ sigma ]=> i2 ->
   n2 =[ sigma ]=> i3 ->
   s = (subb i1 i2 i3) ->
   (ssub a1 n1 n2) =(( sigma ))=> s
where "S =(( X ))=> S'" := (seval S X S').

Example ex6 : scat (sstr "abc") (sstr "def") =(( conf_global ))=> "abcdef".
Proof.
  eapply concat.
  eapply s_const.
  eapply s_const.
  simpl; reflexivity.
Qed.

Example ex7 : scat "z" (sstr "rna") =(( update_conf "z" (update_conf "z" conf_global string_decl) (string_val "ia") ))=> "iarna".
Proof.
  eapply concat.
  eapply s_var.
  eapply s_const.
  simpl; reflexivity.
Qed.

Example ex8 : ssub (sstr "TemaLaPlp") 3 7 =(( conf_global ))=> "aLaPlp".
Proof.
  eapply substring.
  eapply s_const.
  eapply const.
  eapply const.
  simpl; reflexivity.
Qed.
(*--------------- END SEMANTICA SEXP ---------------*)
(*--------------- SEMANTICA Structuri ---------------*)

(*Extragere de valori din struct*)

Definition extractFieldValue (field : Field) :=
match field with
| field s v => v
end.

Definition checkField (field : Field)(s : string) :=
match field with
| field x y => if(string_beq x s) then true else false
end.

Fixpoint getFieldValue (list : (list Field))(s : string) :=
match list with
| nil => error_struct
| (x :: list') => if (checkField x s) then extractFieldValue x else getFieldValue list' s
end.

Definition getStructFieldValue (s : Struct)(f : string) :=
match s with
| struct list => getFieldValue list f
end.

Definition ex_struct := struct ((field "field1" (ptr (offset 1))) :: (field "field2" 3) :: (field "field3" true) :: nil).
Compute (getStructFieldValue ex_struct "field1").
Compute (getStructFieldValue ex_struct "field3").
Compute (getStructFieldValue ex_struct "field5").

(*Setare de valori in struct*)

Fixpoint updateField (list : (list Field))(s : string)(f : FieldValues) :=
match list with
| nil => ((field  s f) :: nil)
| (x :: list') => if (checkField x s) then ((field s f) :: list') else (x :: (updateField list' s f))
end.

Definition setStructFieldValue (s : Struct)(f : string)(t : FieldValues) :=
match s with
| struct list => struct (updateField list f t)
end.

Compute (setStructFieldValue ex_struct "field4" "PLP").
Compute (setStructFieldValue ex_struct "field5" (ref(offset 4))).

(*--------------- END SEMANTICA Structuri ---------------*)
(*--------------- SEMANTICA Pointeri & Referinte ---------------*)

Definition getPointedValue (pointer : ErrorPtr)(conf : Config) :=
match pointer with
| error_ptr => err_assign
| ptr mem => (getConfigMemzoneResult conf mem)
end.

Definition getReferencedValue (reference : ErrorRef)(conf : Config) :=
match reference with
| error_ref => err_assign
| ref mem => (getConfigMemzoneResult conf mem)
end.

Definition setPointer (pointer : ErrorPtr)(mem : Mem) :=
match pointer with
| error_ptr => (ptr mem)
| ptr x => (ptr mem)
end.

Definition ptr1 := (ptr (offset 1)).
Compute (getPointedValue ptr1 conf_global).
Compute (setPointer ptr1 (offset 3)).

(*--------------- END SEMANTICA Pointeri & Referinte ---------------*)
(*--------------- SEMANTICA Switch ---------------*)

Fixpoint evalSwitchInt (s : string)(conf : Config)(l : (list(Pair ErrorNat Stmt))) :=
match l with
| nil => break
| ((pair _ _ x y) :: l') => match (getConfigMemzoneResult conf (getConfigElementOffset conf s)) with
                              | nat_val z => if(ErrorNat_beq z x) then y else (evalSwitchInt s conf l')
                              | _ => (evalSwitchInt s conf l')
                            end
end.

Fixpoint evalSwitchBool (s : string)(conf : Config)(l : (list(Pair ErrorBool Stmt))) :=
match l with
| nil => break
| ((pair _ _ x y) :: l') => match (getConfigMemzoneResult conf (getConfigElementOffset conf s)) with
                              | bool_val z => if(ErrorBool_beq z x) then y else (evalSwitchBool s conf l')
                              | _ => (evalSwitchBool s conf l')
                            end
end.

(*--------------- END SEMANTICA Switch ---------------*)
(*--------------- SEMANTICA Functii ---------------*)

Fixpoint make_conf (list : (list string))(import_conf : Config)(export_conf : Config) : Config :=
match list with
| nil => export_conf
| (smth :: list') => match ((getConfigMemzoneResult import_conf (getConfigElementOffset import_conf smth))) with
                     | nat_val y => (make_conf list' import_conf (update_conf smth (update_conf smth export_conf nat_decl) ((getConfigMemzoneResult import_conf (getConfigElementOffset import_conf smth)))))
                     | bool_val y => (make_conf list' import_conf (update_conf smth (update_conf smth export_conf bool_decl) ((getConfigMemzoneResult import_conf (getConfigElementOffset import_conf smth)))))
                     | _ => (make_conf list' import_conf (update_conf smth export_conf ((getConfigMemzoneResult import_conf (getConfigElementOffset import_conf smth)))))
                     end
end.

(*--------------- END SEMANTICA Functii ---------------*)
(*--------------- SEMANTICA Stmt ---------------*)

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Config -> Config -> Prop :=
(*Declarations*)
| e_int_decl: forall x sigma sigma',
    sigma' = (update_conf x sigma nat_decl) ->
    (int_decl x) -{ sigma }-> sigma'
| e_bool_decl: forall x sigma sigma',
    sigma' = (update_conf x sigma bool_decl) ->
    (boolean_decl x) -{ sigma }-> sigma'
| e_ptr_decl : forall x sigma sigma',
    sigma' = (update_conf x sigma pointer_decl) ->
    (ptr_decl x) -{ sigma }-> sigma'
| e_structure_decl : forall x sigma sigma',
    sigma' = (update_conf x sigma struct_decl) ->
    (structure_decl x) -{ sigma }-> sigma'
| e_str_decl : forall x sigma sigma',
    sigma' = (update_conf x sigma string_decl) ->
    (str_decl x) -{ sigma }-> sigma'
| e_fct_decl : forall x sigma sigma',
    sigma' = (update_conf x sigma func_decl) ->
    (function_decl x) -{ sigma }-> sigma'
(*Sequences*)
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
(*Assignations*)
| e_int_assgn: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update_conf x sigma (nat_val i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_assgn: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update_conf x sigma (bool_val i)) ->
    (x :b= a) -{ sigma }-> sigma'
| e_string_assgn: forall a i x sigma sigma',
    a =(( sigma ))=> i ->
    sigma' = (update_conf x sigma (string_val i)) ->
    (x :s= a) -{ sigma }-> sigma'
| e_ptr_assgn : forall a x i sigma sigma',
    i = (pointer_val (ptr (getConfigElementOffset sigma a))) ->
    sigma' = (update_conf x sigma i) ->
    (x :p= a) -{ sigma }-> sigma'
| e_ref_assgn : forall a x i sigma sigma',
    i = (ref_val (ref (getConfigElementOffset sigma a))) ->
    sigma' = (update_conf x sigma i) ->
    (x :r= a) -{ sigma }-> sigma'
(*Functions*)
| e_void_func : forall n list s sigma sigma' sigma'' sigma''' sigma'''',
   sigma' = (update_conf n sigma (func_val s)) ->
   sigma''' = conf_global ->
   sigma'' = make_conf list sigma' sigma''' ->
   s -{ sigma'' }-> sigma'''' ->
   (void_func n list s) -{ sigma }-> sigma'
| e_int_func : forall x x' n list s sigma sigma' sigma'' sigma''' sigma'''' sigma''''',
   sigma' = (update_conf n sigma (func_val s)) ->
   sigma''' = conf_global ->
   sigma'' = make_conf list sigma' sigma''' ->
   s -{ sigma'' }-> sigma'''' ->
   check_eq_over_types nat_decl (getConfigMemzoneResult sigma' (getConfigElementOffset sigma' x)) = true ->
   sigma''''' = update_conf x sigma' (getConfigMemzoneResult sigma'''' (getConfigElementOffset sigma'''' x')) ->
   (int_func n x x' list s) -{ sigma }-> sigma'''''
| e_bool_func : forall x x' n list s sigma sigma' sigma'' sigma''' sigma'''' sigma''''',
   sigma' = (update_conf n sigma (func_val s)) ->
   sigma''' = conf_global ->
   sigma'' = make_conf list sigma' sigma''' ->
   s -{ sigma'' }-> sigma'''' ->
   check_eq_over_types bool_decl (getConfigMemzoneResult sigma' (getConfigElementOffset sigma' x)) = true ->
   sigma''''' = update_conf x sigma' (getConfigMemzoneResult sigma'''' (getConfigElementOffset sigma'''' x')) ->
   (bool_func n x x' list s) -{ sigma }-> sigma'''''
(*Operatii cu structuri*)
| e_setStruct : forall s s' s'' f t sigma sigma',
    s'' = setStructFieldValue s f t ->
    sigma' = (update_conf s' sigma (struct_val s'')) ->
    (setStructField s s' f t) -{ sigma }-> sigma' 
| e_getStruct : forall s s' sigma sigma',
    sigma' = (update_conf s' sigma (struct_val s)) ->
    (getStruct s s') -{ sigma }-> sigma'
(*Operatii cu pointeri & referinte*)
| e_getPtr : forall p s sigma sigma',
    sigma' = (update_conf s sigma (getPointedValue p sigma)) ->
    (getPtrVal p s) -{ sigma }-> sigma'
| e_getRef : forall r s sigma sigma',
    sigma' = (update_conf s sigma (getReferencedValue r sigma)) ->
    (getRefVal r s) -{ sigma }-> sigma'
| e_setPtr : forall p s sigma,
    p = setPointer(p)(getConfigElementOffset sigma s) ->
    (setPtrVal p s) -{ sigma }-> sigma
(*Switch & Break*)
| e_break : forall sigma,
    (break) -{ sigma }-> sigma
| e_switch_int : forall s1 sigma sigma' list s,
    s1 = (evalSwitchInt s sigma list) ->
    s1 -{ sigma }-> sigma' ->
    (switch_int s list) -{ sigma }-> sigma'
| e_switch_bool : forall s1 sigma sigma' list s,
    s1 = (evalSwitchBool s sigma list) ->
    s1 -{ sigma }-> sigma' ->
    (switch_bool s list) -{ sigma }-> sigma'
(*For & While & If & Ifelse*)
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
| e_ifexec : forall b s s' sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    ifthenelse b s s' -{ sigma }-> sigma'
| e_elseexec : forall b s s' sigma sigma'',
    b ={ sigma }=> false ->
    s' -{ sigma }-> sigma'' ->
    ifthenelse b s s' -{ sigma }-> sigma''
| e_ifexeconly : forall b s sigma sigma',
    b ={ sigma }=> true ->
    s -{ sigma }-> sigma' ->
    ifthen b s -{ sigma }-> sigma'
| e_ifexeconlyfail : forall b s sigma,
    b ={ sigma }=> false ->
    ifthen b s -{ sigma }-> sigma
| e_for : forall a b c s sigma sigma' sigma'',
    a -{ sigma }-> sigma' ->
    while b (s ;; c) -{ sigma' }-> sigma'' ->
    forr a b c s -{ sigma }-> sigma''

where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

Example ex9 : while("x" <' 3)(int_decl "z" ;; "z" :n= 3) -{ update_conf "x" conf_global (nat_val 4) }-> (update_conf "x" conf_global (nat_val 4)).
Proof.
  eapply e_whilefalse.
  eapply b_lessthan.
  eapply var.
  eapply const.
  simpl; reflexivity.
Qed.

Example ex10 : exists sigma', IFF(2 <' 11) THENN (int_decl "z" ;; "z" :n= 3) ENDD -{ conf_global }-> sigma' /\ (getConfigMemzoneResult sigma' (getConfigElementOffset sigma' "z")) = 3.
Proof.
  eexists.
  split.
  - eapply e_ifexeconly.
    eapply b_lessthan.
    eapply const.
    eapply const.
    simpl; reflexivity.
    eapply e_seq.
    eapply e_int_decl;eauto.
    eapply e_int_assgn.
    eapply const;simpl;eauto.
+ unfold update_conf; unfold update_conf; simpl; reflexivity.
- eauto.
Qed.

Definition sample_config := (update_conf "z" (update_conf "z" conf_global nat_decl) 10).
Example ex11 : exists sigma, forr ("x" :n= 2)("x" <' 3)("x" :n= "x" +' 2)("z" :n= "z" +' 1) -{ sample_config }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "z")) = 11.
Proof.
eexists.
split.
- eapply e_for.
  eapply e_int_assgn.
  eapply const.
  eauto.
  eapply e_whiletrue.
  eapply b_lessthan.
  eapply var.
  eapply const.
  simpl; reflexivity.
  eapply e_seq.
  eapply e_seq.
  eapply e_int_assgn.
  eapply add.
  eapply var.
  eapply const.
  simpl; reflexivity.
  eauto.
  eapply e_int_assgn.
  eapply add.
  eapply var.
  eapply const.
  simpl; reflexivity.
  eauto.
  eapply e_whilefalse.
  eapply b_lessthan.
  eapply var.
  eapply const.
  simpl; reflexivity.
- eauto.
Qed.

Definition sample_struct := struct ((field "f1" 10) :: (field "f2" true) :: nil).
Example ex12 : exists sigma, (structure_decl "z" ;; setStructField sample_struct "z" "f1" 11)-{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "z")) = struct ((field "f1" 11) :: (field "f2" true) :: nil).
Proof.
eexists.
split.
- eapply e_seq.
  eapply e_structure_decl.
  eauto.
  eapply e_setStruct.
  eauto.
  eauto.
- eauto.
Qed.

Definition sample_pointer := ptr (offset 1).
Example ex13 : exists sigma, (ptr_decl "z" ;; "z" :p= "y" ;; "c" :r= "x")-{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "z")) = ptr (getConfigElementOffset sigma "y") /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "c")) = ref (getConfigElementOffset sigma "x").
Proof.
eexists.
split.
- eapply e_seq.
  eapply e_ptr_decl.
  eauto.
  eapply e_seq.
  eapply e_ptr_assgn.
  eauto.
  eauto.
  eapply e_ref_assgn.
  eauto.
  eauto.
- split.
  eauto.
  eauto.
Qed.

Example ex14 : exists sigma, (int_decl "z" ;; getPtrVal sample_pointer "z") -{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "z")) = nat_decl.
Proof.
eexists.
split.
- eapply e_seq.
  eapply e_int_decl.
  eauto.
  eapply e_getPtr.
  eauto.
- eauto.
Qed.

Example ex15 : exists sigma, ("x" :n= (num 10) ;; switch_int "x" ((pair _ _ (num 2) ("y" :b= bfalse)) :: (pair _ _ (num 3) ("y" :b= bfalse)) :: (pair _ _ (num 10) ("y" :b= btrue)) :: nil)) -{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "y")) = true.
Proof.
eexists.
split.
- eapply e_seq.
  eapply e_int_assgn.
  eapply const.
  eauto.
  eapply e_switch_int.
  eauto.
  simpl.
  eapply e_bool_assgn.
  eapply b_true.
  eauto.
- eauto.
Qed.

Example ex16 : exists sigma, ("x" :n= (num 10) ;; switch_int "x" ((pair _ _ (num 2) ("y" :b= bfalse)) :: (pair _ _ (num 3) ("y" :b= bfalse)) :: (pair _ _ (num 1) ("y" :b= btrue)) :: nil)) -{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "y")) = bool_decl.
Proof.
eexists.
split.
- eapply e_seq.
  eapply e_int_assgn.
  eapply const.
  eauto.
  eapply e_switch_int.
  eauto.
  simpl.
  eapply e_break.
- eauto.
Qed.

Example ex17 : exists sigma, (int_decl "a" ;; int_decl "b" ;; int_decl "res" ;; (int_func "main" "res" "c" ("a" :: "b" :: nil) ("a" :n= 5 ;; "b" :n= 10 ;; int_decl "c" ;; "c" :n= "a" *' "b")))-{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "res")) = 50.
Proof.
eexists.
split.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_int_func.
eauto.
eauto.
eauto.
eapply e_seq.
eapply e_int_assgn.
eapply const.
eauto.
eapply e_seq.
eapply e_int_assgn.
eapply const.
eauto.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_int_assgn.
eapply times.
eapply var.
eapply var.
eauto.
eauto.
eauto.
eauto.
eauto.
Qed.

Example ex18 : exists sigma, (int_decl "a" ;; "a" :n= 5 ;; int_decl "b" ;; "b" :n= 32 ;; int_decl "res" ;; (int_func "main" "res" "c" ("a" :: "b" :: nil) (int_decl "c" ;; "c" :n= "b" -' "a")))-{ conf_global }-> sigma /\ (getConfigMemzoneResult sigma (getConfigElementOffset sigma "res")) = 27.
Proof.
eexists.
split.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_seq.
eapply e_int_assgn.
eapply const.
eauto.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_seq.
eapply e_int_assgn.
eapply const.
eauto.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_int_func.
eauto.
eauto.
eauto.
eapply e_seq.
eapply e_int_decl.
eauto.
eapply e_int_assgn.
eapply substract.
eapply var.
eapply var.
eauto.
eauto.
eauto.
eauto.
eauto.
Qed.

(*--------------- END SEMANTICA Stmt ---------------*)



(* ~~~ END SEMANTICA ~~~*)
Require Import List.
Import ListNotations.
Require Import Arith.
(* ~~~ COMPILATOR AEXP + BEXP ~~~*)


(*--------------- AEXP ---------------*)

Fixpoint interpret_aexp (e : AExp) (conf : Config) : nat :=
match e with
| anum x => match x with
            | num y => y
            | error_nat => 0
            end
| avar x => match (getConfigMemzoneResult conf (getConfigElementOffset conf x)) with
            | nat_val (num y) => y
            | _ => 0
            end
| aplus x1 x2 => (interpret_aexp x1 conf) + (interpret_aexp x2 conf)
| asub x1 x2 => (interpret_aexp x1 conf) - (interpret_aexp x2 conf)
| amul x1 x2 => (interpret_aexp x1 conf) * (interpret_aexp x2 conf)
| adiv x1 x2 => (interpret_aexp x1 conf) / (interpret_aexp x2 conf)
| amod x1 x2 => (interpret_aexp x1 conf) mod (interpret_aexp x2 conf)
end.

Compute (interpret_aexp (10 +' (avar "x")) (update_conf "x" conf_global 4)).
Compute (interpret_aexp (6 %' 5) conf_global).
Compute (interpret_aexp (4 -' 6) conf_global).
Compute (interpret_aexp ((avar "x") /' 5) (update_conf "x" conf_global 15)).

Inductive instruction_aexp :=
| push_const : nat -> instruction_aexp
| push_var : string -> instruction_aexp
| adunare : instruction_aexp
| scadere : instruction_aexp
| inmultire : instruction_aexp
| impartire : instruction_aexp
| modd : instruction_aexp.

Definition stack_aexp := list nat.
Definition run_instruction_aexp (i : instruction_aexp) (conf : Config) (s : stack_aexp) : stack_aexp :=
match i with
| push_const c => (c :: s)
| push_var x => (match (getConfigMemzoneResult conf (getConfigElementOffset conf x)) with
                | nat_val (num y) => y
                | _ => 0
                end :: s)
| adunare => match s with
            | n1 :: n2 :: s' => ((n1 + n2) :: s')
            | _ => s
            end
| scadere => match s with
            | n1 :: n2 :: s' => ((n1 - n2) :: s')
            | _ => s
            end
| inmultire => match s with
            | n1 :: n2 :: s' => ((n1 * n2) :: s')
            | _ => s
            end
| modd => match s with
            | n1 :: n2 :: s' => ((n1 mod n2) :: s')
            | _ => s
            end
| impartire => match s with
            | n1 :: n2 :: s' => ((n1 / n2) :: s')
            | _ => s
            end
end.

Compute (run_instruction_aexp (push_const 44) conf_global []).
Compute (run_instruction_aexp (push_var "x") conf_global []).
Compute (run_instruction_aexp inmultire conf_global [10;20;30]).
Compute (run_instruction_aexp scadere conf_global [36;21;10]).

Fixpoint run_instructions_aexp (l : list instruction_aexp)(conf : Config)(stack : stack_aexp) : stack_aexp :=
match l with
| [] => stack
| i :: l' => run_instructions_aexp l' conf (run_instruction_aexp i conf stack)
end.

Definition p1 := (push_const 5 :: push_var "a" :: nil).
Definition p2 := (push_const 11 :: push_var "x" :: adunare :: push_var "x" :: inmultire :: push_const 62 :: scadere :: nil).
Compute run_instructions_aexp p1 (update_conf "a" (update_conf "a" conf_global nat_decl) 5) (nil).
Compute run_instructions_aexp p2 (update_conf "x" conf_global 3) (nil).

Fixpoint compile_aexp (e : AExp) : list instruction_aexp :=
match e with
| anum x => [push_const match x with
            | num y => y
            | error_nat => 0
            end]
| avar x => [push_var x]
| aplus x1 x2 => (compile_aexp x1) ++ (compile_aexp x2) ++ [adunare]
| asub x1 x2 => (compile_aexp x2) ++ (compile_aexp x1) ++ [scadere]
| amul x1 x2 => (compile_aexp x1) ++ (compile_aexp x2) ++ [inmultire]
| adiv x1 x2 => (compile_aexp x2) ++ (compile_aexp x1) ++ [impartire]
| amod x1 x2 => (compile_aexp x2) ++ (compile_aexp x1) ++ [modd]
end.

Compute compile_aexp (2 +' (avar "x")).
Compute compile_aexp (5 %' (avar "x") *' 6).
Compute interpret_aexp (2 *' (avar "x") +' 4) (update_conf "x" conf_global 3).
Compute interpret_aexp (5 *' (avar "x") /' 4 -' 1) (update_conf "x" conf_global 3).

Lemma soundness_helper_aexp :
forall e conf stack l,
run_instructions_aexp (compile_aexp e ++ l) conf stack =
run_instructions_aexp l conf ((interpret_aexp e conf) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite PeanoNat.Nat.add_comm.
    reflexivity.
- rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
- rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    rewrite PeanoNat.Nat.mul_comm.
    reflexivity.
- rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
- rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
    Qed.

Theorem soundness_aexp :
  forall e conf,
  run_instructions_aexp (compile_aexp e) conf [] =
  [interpret_aexp e conf].
Proof.
intros.
Check app_nil_r.
rewrite <- app_nil_r with (l := (compile_aexp e)).
rewrite soundness_helper_aexp.
simpl.
trivial.
Qed.

(*--------------- END AEXP ---------------*)
(*--------------- BEXP ---------------*)

Fixpoint interpret_bexp (e : BExp) (conf : Config) : bool :=
match e with
| berror => false
| btrue => true
| bfalse => false
| bbool x => match x with
            | boolean y => y
            | error_bool => false
            end
| bvar x => match (getConfigMemzoneResult conf (getConfigElementOffset conf x)) with
            | bool_val (boolean y) => y
            | _ => false
            end
| blt x1 x2 => leb (interpret_aexp x1 conf) (interpret_aexp x2 conf)
| bnot x1 => negb (interpret_bexp x1 conf)
| band x1 x2 => andb (interpret_bexp x1 conf) (interpret_bexp x2 conf)
| bor x1 x2 => orb (interpret_bexp x1 conf) (interpret_bexp x2 conf)
end.

Compute (interpret_bexp (2 <' (avar "x")) (update_conf "x" conf_global 4)).
Compute (interpret_bexp (!' (bfalse &&' btrue)) conf_global).
Compute (interpret_bexp ((btrue) ||' (bfalse)) conf_global).
Compute (interpret_bexp (((avar "x") /' 5) <' 2) (update_conf "x" conf_global 15)).

Inductive instruction_bexp :=
| push_bconst : bool -> instruction_bexp
| push_bvar : string -> instruction_bexp
| maimic : AExp -> AExp -> instruction_bexp
| negatie : instruction_bexp
| si : instruction_bexp
| sau : instruction_bexp.

Definition stack_bexp := list bool.
Definition run_instruction_bexp (i : instruction_bexp) (conf : Config) (s : stack_bexp) : stack_bexp :=
match i with
| push_bconst c => (c :: s)
| push_bvar x => (match (getConfigMemzoneResult conf (getConfigElementOffset conf x)) with
                | bool_val (boolean y) => y
                | _ => false
                end :: s)
| maimic x1 x2 => ((leb (interpret_aexp x1 conf) (interpret_aexp x2 conf)) :: s)
| negatie => match s with
            | n1 :: s' => ((negb n1) :: s')
            | _ => s
            end
| si => match s with
            | n1 :: n2 :: s' => ((andb n2 n1) :: s')
            | _ => s
            end
| sau => match s with
            | n1 :: n2 :: s' => ((orb n2 n1) :: s')
            | _ => s
            end
end.

Compute (run_instruction_bexp (maimic 1 2) conf_global []).
Compute (run_instruction_bexp (push_bvar "y") conf_global []).
Compute (run_instruction_bexp si conf_global [true;true;false]).
Compute (run_instruction_bexp negatie conf_global [false;false;false]).

Fixpoint run_instructions_bexp (l : list instruction_bexp)(conf : Config)(stack : stack_bexp) : stack_bexp :=
match l with
| [] => stack
| i :: l' => run_instructions_bexp l' conf (run_instruction_bexp i conf stack)
end.

Definition p1' := (push_bconst true :: push_bvar "k" :: nil).
Definition p2' := (push_bconst true :: push_bvar "y" :: si :: push_bvar "x" :: sau :: push_bconst true :: negatie :: nil).
Compute run_instructions_bexp p1' (update_conf "a" (update_conf "k" conf_global bool_decl) true) [].
Compute run_instructions_bexp p2' (update_conf "y" conf_global true) [].

Fixpoint compile_bexp (e : BExp) : list instruction_bexp :=
match e with
| berror => [push_bconst false]
| btrue => [push_bconst true]
| bfalse => [push_bconst false]
| bbool x => [push_bconst match x with
            | boolean y => y
            | error_bool => false
            end]
| bvar x => [push_bvar x]
| blt x1 x2 => [maimic x1 x2]
| band x1 x2 => (compile_bexp x1) ++ (compile_bexp x2) ++ [si]
| bor x1 x2 => (compile_bexp x1) ++ (compile_bexp x2) ++ [sau]
| bnot x1 => (compile_bexp x1) ++ [negatie]
end.

Compute compile_bexp (2 <' 3).
Compute compile_bexp (btrue ||' bfalse).
Compute interpret_bexp ((2 <' (avar "x")) &&' btrue) (update_conf "x" conf_global true).
Compute interpret_bexp (!' (5 <' (avar "x"))) (update_conf "x" conf_global 3).

Lemma soundness_helper_bexp :
forall e conf stack l,
run_instructions_bexp (compile_bexp e ++ l) conf stack =
run_instructions_bexp l conf ((interpret_bexp e conf) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite IHe.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
Qed.

Theorem soundness_bexp :
forall e conf,
run_instructions_bexp (compile_bexp e) conf [] =
[interpret_bexp e conf].
Proof.
intros.
Check app_nil_r.
rewrite <- app_nil_r with (l := (compile_bexp e)).
rewrite soundness_helper_bexp.
simpl.
trivial.
Qed.
(*--------------- END BEXP ---------------*)