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

(** Interface to the sum type. *)
Module Sum.
  Parameter t : Type -> Type -> Type.
  Extract Constant t "'a" "'b" => "('a, 'b) IoSystem.Sum.t".

  Parameter destruct : forall {A B C : Type}, t A B -> (A -> C) -> (B -> C) -> C.
  Extract Constant destruct => "IoSystem.Sum.destruct".

  Definition to_coq {A B : Type} (s : t A B) : A + B :=
    destruct s inl inr.
End Sum.

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

  (** First. *)
  Parameter first : forall {A B : Type}, t A -> t B -> t (Sum.t A B).
  Extract Constant first => "IoSystem.first".

  (** Run. *)
  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

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
  Parameter eval : String.t -> list String.t ->
    t (option (BigInt.t * String.t * String.t)).
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
  | System.Eval command args =>
    let command := String.of_lstring command in
    let args := List.map String.of_lstring args in
    Lwt.bind (Lwt.eval command args) (fun result =>
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
Fixpoint eval {A : Type} (x : C.t System.effect A) : Lwt.t A.
  destruct x as [A x | command | A B x f | A B x y | A B x y].
  - exact (Lwt.ret x).
  - exact (eval_command command).
  - exact (Lwt.bind (eval _ x) (fun x => eval _ (f x))).
  - exact (Lwt.join (eval _ x) (eval _ y)).
  - exact (
      Lwt.bind (Lwt.first (eval _ x) (eval _ y)) (fun s =>
      Lwt.ret @@ Sum.to_coq s)).
Defined.

(** Run the main function. *)
Definition run (main : list LString.t -> C.t System.effect unit) : unit :=
  let argv := List.map String.to_lstring Sys.argv in
  Lwt.run (Extraction.eval (main argv)).
