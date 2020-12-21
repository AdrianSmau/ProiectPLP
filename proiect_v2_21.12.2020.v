Require Import Strings.String.
Local Open Scope string_scope.
Local Open Scope list_scope.
Scheme Equality for string.

(*--------------- TIPURI DE DATE ---------------*)

Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.

Coercion num: nat >-> ErrorNat.

Check num 3.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.

Coercion boolean: bool >-> ErrorBool.

Check boolean true.

Inductive ErrorString :=
  | error_string : ErrorString
  | Sstring : string -> ErrorString.

Coercion Sstring: string >-> ErrorString.

Check Sstring "PLP".

Inductive ErrorPtr :=
  | error_ptr : ErrorPtr
  | ptr : string -> ErrorPtr.

Check ptr "x".

Inductive ErrorRef :=
  | error_ref : ErrorRef
  | ref : string -> ErrorRef.

Check ref "y".

(*--------------- END TIPURI DE DATE ---------------*)

(*Cele 2 tipuri de date, semantic, vor prelua offset-ul variabilelor asignate*)

(*--------------- STRUCT-URI ---------------*)

Inductive FieldValues :=
| nat_value : ErrorNat -> FieldValues
| bool_value : ErrorBool -> FieldValues
| ptr_value : ErrorPtr -> FieldValues
| ref_value : ErrorRef -> FieldValues
| string_value : ErrorString -> FieldValues.

Coercion nat_value: ErrorNat >-> FieldValues.
Coercion bool_value: ErrorBool >-> FieldValues.
Coercion ptr_value: ErrorPtr >-> FieldValues.
Coercion ref_value: ErrorRef >-> FieldValues.
Coercion string_value: ErrorString >-> FieldValues.

Inductive Field :=
| field : string -> FieldValues -> Field.

Check (field "field1" "x").
Check (field "field1" (ptr "x")).

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
  | svar : string -> SExp
  | scat : SExp -> SExp -> SExp
  | scpy : SExp -> SExp -> SExp
  | slength : SExp -> nat -> SExp.

Coercion svar: string >-> SExp.

Notation "A +s B" := (scat A B) (at level 54,left associativity).
Notation "A +c B" := (scpy A B) (at level 56, left associativity).
Notation "'len' A" := (slength A) (at level 55).

(* VALORILE DE RETURN ALE FUNCTIILOR*)

Inductive ReturnType :=
  | void : ReturnType
  | nat_return : ReturnType
  | bool_return : ReturnType
  | string_return : ReturnType.

(* PAIR PENTRU SWITCH *)

Inductive Pair (T1 T2 : Type) :=
  | pair (t1 : T1) (t2 : T2).

Inductive Stmt :=
| int_decl: string -> Stmt
| boolean_decl: string -> Stmt
| ptr_decl: string -> Stmt
| str_decl : string -> Stmt
| structure_decl : string -> Stmt
| assgn_ptr: string -> string -> Stmt
| assgn_ref: string -> string -> Stmt
| assgn_int : string -> AExp -> Stmt
| assgn_bool : string -> BExp -> Stmt
| assgn_string : string -> SExp -> Stmt
| assgn_func : ReturnType -> string -> (list AExp) -> Stmt -> Stmt
| assgn_struct : string -> Struct -> Stmt
| getStructField : string -> string -> Stmt
| setStructField : string -> string -> FieldValues -> Stmt
| break : Stmt
| continue : Stmt
| switch_int : string -> list (Pair ErrorNat Stmt) -> Stmt
| switch_bool : string -> list (Pair ErrorBool Stmt) -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

(*Un pointer poate fi declarat inainte de a fi initializat, insa o referinta nu*)

Notation "'int' X" := (int_decl X) (at level 90).
Notation "'boolean' X" := (boolean_decl X) (at level 90).
Notation "'str' X" := (str_decl X) (at level 90).
Notation "'structure' X" := (structure_decl X) (at level 90).
Notation "'*' X" := (ptr_decl X) (at level 90).
Notation "X :n= A" := (assgn_int X A) (at level 90).
Notation "X :b= A" := (assgn_bool X A) (at level 90).
Notation "X :p= A" := (assgn_ptr X A) (at level 90).
Notation "X :r= A" := (assgn_ref X A) (at level 90).
Notation "X :s= A" := (assgn_string X A) (at level 90).
Notation "X :struct= A" := (assgn_struct X A) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).

Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).
Reserved Notation "B ={ S }=> B'" (at level 70).
Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

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
(* --------------- MEM + MEMLAYER (GLOBAL + BLANK) + ENV (GLOBAL + BLANK) + STACK(OF ENV) + CONFIG ---------------*)

Inductive Mem :=
  | mem_default : Mem
  | offset : nat -> Mem.

Scheme Equality for Mem.

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
    if(Mem_beq s (offset 1)) then nat_decl
    else if (Mem_beq s (offset 2)) then bool_decl
      else undecl.

Definition mem_blank : MemLayer :=
  fun s =>
    if(Mem_beq s (offset 1)) then nat_decl
    else if (Mem_beq s (offset 2)) then bool_decl
      else undecl.

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
        | func_val a => (config (nbr) (update_env env s (offset (nbr))) (update_mem mem (update_env env s (offset (nbr))) s (offset (nbr)) r) (env :: stack))
        | nat_val a => (config (nbr) (update_env env s (offset (nbr))) (update_mem mem (update_env env s (offset (nbr))) s (offset (nbr)) r) stack)
        | bool_val a => (config (nbr) (update_env env s (offset (nbr))) (update_mem mem (update_env env s (offset (nbr))) s (offset (nbr)) r) stack)
        | struct_val a => (config (nbr) (update_env env s (offset (nbr))) (update_mem mem (update_env env s (offset (nbr))) s (offset (nbr)) r) stack)
        | pointer_val a => (config (nbr) (update_env env s (offset (nbr))) (update_mem mem (update_env env s (offset (nbr))) s (offset (nbr)) r) stack)
        | ref_val a => (config (nbr) (update_env env s (offset (nbr))) (update_mem mem (update_env env s (offset (nbr))) s (offset (nbr)) r) stack)
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
                                  | nil => env_blank
                                  | (c :: stack') => c
                                  end
end.

Compute (getConfigElementOffset (update_conf "z" conf_global func_decl) "z").
Compute (getConfigElementOffset (update_conf "z" (update_conf "z" conf_global func_decl) (func_val (int_decl "k"))) "z").
Compute (getConfigMemzoneResult (update_conf "z" (update_conf "z" conf_global nat_decl) (nat_val 6)) (offset 3)).
Compute (getConfigMemzoneResult (update_conf "z" conf_global func_decl) (offset 3)).
Compute (getConfigLastMemzone (update_conf "z" conf_global func_decl)).
Compute getConfigMemzoneResult (update_conf "z" (update_conf "z" conf_global func_decl) (func_val (int_decl "k"))) (offset 3).

(* --------------- END MEM + MEMLAYER (GLOBAL + BLANK) + ENV (GLOBAL + BLANK) + STACK(OF ENV) + CONFIG ---------------*)
(* --------------- GLOBAL VARIABLES LIST ---------------*)

Definition string_list := list string.

Definition global_vars : string_list := ("x" :: "y" :: nil).

(* --------------- END GLOBAL VARIABLES LIST ---------------*)

(*TO DO : SEMANTICA + GET,SET PENTRU STRUCT*)





















