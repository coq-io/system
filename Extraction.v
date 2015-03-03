(** Extraction to OCaml. New primitives are defined in `extraction/utils.ml`. *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Io.All.
Require Unix.

Import ListNotations.
Local Open Scope type.

(** Interface with the OCaml strings. *)
Module String.
  (** The OCaml `string` type. *)
  Parameter t : Type.
  Extract Constant t => "string".

  (** Export to an OCaml string. *)
  Parameter of_lstring : LString.t -> t.
  Extract Constant of_lstring => "IoEffectsUnix.String.of_lstring".

  (** Import an OCaml string. *)
  Parameter to_lstring : t -> LString.t.
  Extract Constant to_lstring => "IoEffectsUnix.String.to_lstring".
End String.

(** Unbounded integers. *)
Module BigInt.
  (** The OCaml's `bigint` type. *)
  Definition t : Type := bigint.

  (** Export to a `Z`. *)
  Definition to_Z : t -> Z := z_of_bigint.
End BigInt.

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

  (** Run. *)
  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  (** List the files of a directory. *)
  Parameter list_files : String.t -> t (option (list String.t)).
  Extract Constant list_files => "IoEffectsUnix.list_files".

  (** The the content of a file. *)
  Parameter read_file : String.t -> t (option String.t).
  Extract Constant read_file => "IoEffectsUnix.read_file".

  (** Update (or create) a file with some content. *)
  Parameter write_file : String.t -> String.t -> t bool.
  Extract Constant write_file => "IoEffectsUnix.write_file".

  (** Delete a file. *)
  Parameter delete_file : String.t -> t bool.
  Extract Constant delete_file => "IoEffectsUnix.delete_file".

  (** Run a command. *)
  Parameter system : String.t -> t (option bool).
  Extract Constant system => "IoEffectsUnix.system".

  (** Print a message on the standard output. *)
  Parameter print : String.t -> t bool.
  Extract Constant print => "IoEffectsUnix.print".

  (** Read a line on the standard input. *)
  Parameter read_line : unit -> t (option String.t).
  Extract Constant read_line => "IoEffectsUnix.read_line".
End Lwt.

(** Evaluate a command using Lwt. *)
Definition eval_command (c : Effects.command Unix.effects)
  : Lwt.t (Effects.answer Unix.effects c) :=
  match c return (Lwt.t (Effects.answer Unix.effects c)) with
  | Unix.ListFiles folder =>
    Lwt.bind (Lwt.list_files @@ String.of_lstring folder) (fun files =>
    Lwt.ret @@ Option.bind files (fun files =>
    Some (List.map String.to_lstring files)))
  | Unix.ReadFile file_name =>
    Lwt.bind (Lwt.read_file @@ String.of_lstring file_name) (fun content =>
    Lwt.ret @@ option_map String.to_lstring content)
  | Unix.WriteFile file_name content =>
    let file_name := String.of_lstring file_name in
    let content := String.of_lstring content in
    Lwt.write_file file_name content
  | Unix.DeleteFile file_name =>
    Lwt.delete_file @@ String.of_lstring file_name
  | Unix.System command => Lwt.system (String.of_lstring command)
  | Unix.Print message =>
    let message := String.of_lstring message in
    Lwt.print message
  | Unix.ReadLine =>
    Lwt.bind (Lwt.read_line tt) (fun line =>
    Lwt.ret @@ option_map String.to_lstring line)
  end.

(** Evaluate an expression using Lwt. *)
Fixpoint eval {A : Type} (x : C.t Unix.effects A) : Lwt.t A :=
  match x with
  | C.Ret _ x => Lwt.ret x
  | C.Call command => eval_command command
  | C.Let _ _ x f => Lwt.bind (eval x) (fun x => eval (f x))
  end.
