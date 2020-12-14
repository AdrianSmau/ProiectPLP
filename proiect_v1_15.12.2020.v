Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.
Inductive ErrorNat :=
  | error_nat : ErrorNat
  | num : nat -> ErrorNat.
Coercion num: nat >-> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool
  | boolean : bool -> ErrorBool.
Coercion boolean: bool >-> ErrorBool.

Inductive Vars :=
  | undecl : Vars
  | err_assign : Vars
  | nat_decl : Vars
  | bool_decl : Vars
  | nat_val : ErrorNat -> Vars
  | bool_val : ErrorBool -> Vars.

Scheme Equality for Vars.

Definition Env := string -> Vars.

(*Definition check_types (s1 : Vars) (s2 : Vars) : bool :=
  match s1 with
    | err_assign => false
    | undecl => match s2 with
                  | undecl => true
                  | _ => false
                end
    | nat_decl => match s2 with
                    | nat_val x => true
                    | nat_decl => true
                    | _ => false
                  end
    | bool_decl => match s2 with
                    | bool_val x => true
                    | bool_decl => true
                    | _ => false
                    end
    | nat_val x => match s2 with
                    | nat_val y => true
                    | nat_decl => true
                    | _ => false
                  end
    | bool_val x => match s2 with
                    | bool_val y => true
                    | bool_decl => true
                    | _ => false
                   end
    end.*)

(*Functia nefolosita*)

Definition env : Env := fun s =>
    if(string_beq s "x")
    then nat_val 0
    else if(string_beq s "y")
         then nat_val 0
         else if(string_beq s "a")
              then bool_val false
              else if(string_beq s "b")
                   then bool_val false
                   else undecl.

Definition update (env : Env) (x : string) (v : Vars) : Env :=
  match v with
  | err_assign => fun y =>
    if (string_eq_dec x y)
    then v
    else (env y)
  | undecl => fun y =>
    if (string_eq_dec x y)
    then err_assign
    else (env y)
  | nat_decl => fun y =>
    if (string_eq_dec x y)
    then match (env y) with
          | undecl => v
          | _ => err_assign
          end
    else (env y)
  | bool_decl => fun y =>
    if (string_eq_dec x y)
    then match (env y) with
          | undecl => v
          | _ => err_assign
          end
    else (env y)
  | bool_val a => fun y =>
    if (string_eq_dec x y)
    then match (env y) with
          | bool_val b => v
          | bool_decl => v
          | _ => err_assign
          end
    else (env y)
  | nat_val a => fun y =>
    if (string_eq_dec x y)
    then match (env y) with
          | nat_val b => v
          | nat_decl => v
          | _ => err_assign
          end
    else (env y)
  end.

Compute (env "k").
Compute (update env "k" (bool_decl) "k").
Compute (update (update env "x" (nat_val 10)) "a" (bool_val true) "a").

Notation "'bool' S" := (update env S bool_decl) (at level 0).
Notation "'int' S" := (update env S nat_decl) (at level 0).
Compute (bool "f") "f".
Compute (bool "a") "a".
Compute (int "x") "x".
Compute (int "x") "y".

Inductive AExp :=
| avar : string -> AExp
| anum : ErrorNat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| asub : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp.

Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp.

Notation "A +' B" := (aplus A B) (at level 11).
Notation "A *' B" := (amul A B) (at level 8).
Notation "A /' B" := (asub A B) (at level 8).
Notation "A %' B" := (amod A B) (at level 9).
Notation "A -' B" := (amin A B) (at level 11).

Check ("x" +' 3).
Check ("y" /' "z").

Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

(*semantica AExp aici*)

Inductive BExp :=
| bvar : string -> BExp
| btrue : BExp
| bfalse : BExp
| blt : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp.

Notation "A <' B" := (blt A B) (at level 70).
Notation "!' A" := (bnot A) (at level 51, left associativity).
Notation "A &&' B" := (band A B) (at level 52, left associativity).
Notation "A ||' B" := (bor A B) (at level 53, left associativity).

Check ("a" <' "b").
Check (!' (bvar "x") ||' (bvar "y")).

Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

(*semantica BExp aici*)

Inductive Stmt :=
| assgn_int : string -> AExp -> Stmt
| assgn_bool : string -> BExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| forr : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

Notation "X :n= A" := (assgn_int X A) (at level 90).
Notation "X :b= A" := (assgn_bool X A) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).

(*semantica Stmt aici*)
(*Compilator + netriviale aici*)




























