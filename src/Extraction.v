(** Extraction to OCaml. New primitives are defined in `extraction/utils.ml`. *)
Require Import Coq.Lists.List.
Require Import Coq.PArith.PArith.
Require Import Coq.ZArith.ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Io.All.
Require System.

Import ListNotations.
Local Open Scope type.

(** Usefull values to define fixpoints. *)
Module Loop.
  Parameter infinity : nat.
  Extract Constant infinity => "let rec inf = S inf in inf".

  Parameter error : forall {A B}, A -> B.
  Extract Constant error =>
    "fun _ -> failwith ""Unexpected end of infinite loop.""".
End Loop.

(** Interface to the Big_int library. *)
Module BigInt.
  (** The OCaml's `big_int` type. *)
  Parameter t : Type.
  Extract Constant t => "Big_int.big_int".

  Parameter to_Z_aux : forall {Z positive : Type},
    t ->
    Z -> (positive -> Z) -> (positive -> Z) ->
    positive -> (positive -> positive) -> (positive -> positive) ->
    Z.
  Extract Constant to_Z_aux => "IoSystem.Big.to_Z_aux".

  (** Export to a `Z`. *)
  Definition to_Z (big : t) : Z :=
    to_Z_aux big Z0 Zpos Zneg xH xO xI.
End BigInt.

(** Interface with the OCaml strings. *)
Module String.
  (** The OCaml `string` type. *)
  Parameter t : Type.
  Extract Constant t => "string".

  (** Export to an OCaml string. *)
  Parameter of_lstring : LString.t -> t.
  Extract Constant of_lstring => "IoSystem.String.of_lstring".

  (** Import an OCaml string. *)
  Parameter to_lstring : t -> LString.t.
  Extract Constant to_lstring => "IoSystem.String.to_lstring".
End String.

(** Interface to the Sys library. *)
Module Sys.
  (** The command line arguments of the program. *)
  Parameter argv : list String.t.
  Extract Constant argv => "IoSystem.argv".
End Sys.

(** Interface to the Lwt library. *)
Module Lwt.
  (** The `Lwt.t` type. *)
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a Lwt.t".

  (** Return. *)
  Parameter ret : forall {A : Type}, A -> t A.
  Extract Constant ret => "Lwt.return".

  (** Bind. *)
  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.
  Extract Constant bind => "Lwt.bind".

  (** Join. *)
  Parameter join : forall {A B : Type}, t A -> t B -> t (A * B).
  Extract Constant join => "IoSystem.join".

  (** Choose. *)
  Parameter choose : forall {A : Type}, t A -> t A -> t A.
  Extract Constant choose => "IoSystem.choose".

  (** Launch. *)
  Parameter launch : forall {A : Type}, t A -> A.
  Extract Constant launch => "Lwt_main.run".

  (** List the files of a directory. *)
  Parameter list_files : String.t -> t (option (list String.t)).
  Extract Constant list_files => "IoSystem.list_files".

  (** The the content of a file. *)
  Parameter read_file : String.t -> t (option String.t).
  Extract Constant read_file => "IoSystem.read_file".

  (** Update (or create) a file with some content. *)
  Parameter write_file : String.t -> String.t -> t bool.
  Extract Constant write_file => "IoSystem.write_file".

  (** Delete a file. *)
  Parameter delete_file : String.t -> t bool.
  Extract Constant delete_file => "IoSystem.delete_file".

  (** Run a command. *)
  Parameter system : String.t -> t (option bool).
  Extract Constant system => "IoSystem.system".

  (** Run a command controlling the outputs. *)
  Parameter eval : list String.t -> t (option (BigInt.t * String.t * String.t)).
  Extract Constant eval => "IoSystem.eval".

  (** Print a message on the standard output. *)
  Parameter print : String.t -> t bool.
  Extract Constant print => "IoSystem.print".

  (** Read a line on the standard input. *)
  Parameter read_line : unit -> t (option String.t).
  Extract Constant read_line => "IoSystem.read_line".
End Lwt.

(** Evaluate a command using Lwt. *)
Definition eval_command (c : Effect.command System.effect)
  : Lwt.t (Effect.answer System.effect c) :=
  match c return (Lwt.t (Effect.answer System.effect c)) with
  | System.ListFiles folder =>
    Lwt.bind (Lwt.list_files @@ String.of_lstring folder) (fun files =>
    Lwt.ret @@ Option.bind files (fun files =>
    Some (List.map String.to_lstring files)))
  | System.ReadFile file_name =>
    Lwt.bind (Lwt.read_file @@ String.of_lstring file_name) (fun content =>
    Lwt.ret @@ option_map String.to_lstring content)
  | System.WriteFile file_name content =>
    let file_name := String.of_lstring file_name in
    let content := String.of_lstring content in
    Lwt.write_file file_name content
  | System.DeleteFile file_name =>
    Lwt.delete_file @@ String.of_lstring file_name
  | System.System command => Lwt.system (String.of_lstring command)
  | System.Eval command =>
    let command := List.map String.of_lstring command in
    Lwt.bind (Lwt.eval command) (fun result =>
    Lwt.ret (result |> option_map (fun result =>
    match result with
    | (status, output, err) =>
      (BigInt.to_Z status, String.to_lstring output, String.to_lstring err)
    end)))
  | System.Print message =>
    let message := String.of_lstring message in
    Lwt.print message
  | System.ReadLine =>
    Lwt.bind (Lwt.read_line tt) (fun line =>
    Lwt.ret @@ option_map String.to_lstring line)
  end.

(** Evaluate an expression using Lwt. *)
Fixpoint eval {A} (x : C.t System.effect A) : Lwt.t A.
  destruct x as [A x | command | A B x f | A x1 x2 | A B x y].
  - exact (Lwt.ret x).
  - exact (eval_command command).
  - exact (Lwt.bind (eval _ x) (fun x => eval _ (f x))).
  - exact (Lwt.choose (eval _ x1) (eval _ x2)).
  - exact (Lwt.join (eval _ x) (eval _ y)).
Defined.

(** Launch the main function. *)
Definition launch (main : list LString.t -> C.t System.effect unit) : unit :=
  let argv := List.map String.to_lstring Sys.argv in
  Lwt.launch (eval (main argv)).

Module I.
  Fixpoint eval_aux {A} (steps : nat) (x : C.I.t System.effect A) : Lwt.t A :=
    match steps with
    | O => Loop.error tt
    | S steps =>
      match x with
      | C.I.Ret v => Lwt.ret v
      | C.I.Call c => eval_command c
      | C.I.Let x f =>
        Lwt.bind (eval_aux steps x) (fun v_x => eval_aux steps (f v_x))
      | C.I.Choose x1 x2 => Lwt.choose (eval_aux steps x1) (eval_aux steps x2)
      | C.I.Join x y => Lwt.join (eval_aux steps x) (eval_aux steps y)
      end
    end.

  Definition eval {A} (x : C.I.t System.effect A) : Lwt.t A :=
    eval_aux Loop.infinity x.

  Definition launch (main : list LString.t -> C.I.t System.effect unit)
    : unit :=
    let argv := List.map String.to_lstring Sys.argv in
    Lwt.launch (eval (main argv)).
End I.
