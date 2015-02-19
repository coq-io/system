Require Import ListString.All.
Require Import IoEffects.All.

Inductive t :=
(** List the files of a directory. *)
| ListFiles (directory : LString.t)
(** Read the content of a file. *)
| ReadFile (file_name : LString.t)
(** Update (or create) a file with some content. *)
| WriteFile (file_name : LString.t) (content : LString.t)
(** Delete a file. *)
| DeleteFile (file_name : LString.t)
(** Run a command. *)
| System (command : LString.t)
(** Print a message on the standard output. *)
| Print (message : LString.t).

(** The type of an answer for a command depends on the value of the command. *)
Definition answer (command : t) : Type :=
  match command with
  | ListFiles _ => option (list LString.t)
  | ReadFile _ => option LString.t
  | WriteFile _ _ => bool
  | DeleteFile _ => bool
  | System _ => option bool
  | Print _ => bool
  end.

Definition effects : Effects.t := {|
  Effects.command := t;
  Effects.answer := answer |}.
