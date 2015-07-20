(** Extraction to OCaml. *)
Require Import Coq.Lists.List.
Require Import ErrorHandlers.All.
Require Import Extraction.Loop.
Require Import Extraction.Lwt.
Require Import Extraction.Sys.
Require Import FunctionNinjas.All.
Require Import Io.All.
Require Import ListString.All.
Require System.

Import ListNotations.
Local Open Scope type.

(** Evaluate a command using Lwt. *)
Definition eval_command (c : Effect.command System.effect)
  : Lwt.t (Effect.answer System.effect c) :=
  match c return (Lwt.t (Effect.answer System.effect c)) with
  | System.ListFiles folder =>
    Lwt.bind (Lwt.list_files @@ String.of_lstring folder) (fun files =>
    Lwt.ret @@ Option.map files (fun files =>
    List.map String.to_lstring files))
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
      | C.I.Ret _ v => Lwt.ret v
      | C.I.Call c => eval_command c
      | C.I.Let _ _ x f =>
        Lwt.bind (eval_aux steps x) (fun v_x => eval_aux steps (f v_x))
      | C.I.Choose _ x1 x2 => Lwt.choose (eval_aux steps x1) (eval_aux steps x2)
      | C.I.Join _ _ x y => Lwt.join (eval_aux steps x) (eval_aux steps y)
      end
    end.

  Definition eval {A} (x : C.I.t System.effect A) : Lwt.t A :=
    eval_aux Loop.infinity x.

  Definition launch (main : list LString.t -> C.I.t System.effect unit)
    : unit :=
    let argv := List.map String.to_lstring Sys.argv in
    Lwt.launch (eval (main argv)).
End I.
