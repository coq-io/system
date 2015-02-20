Require Import Coq.Lists.List.
Require Import ListString.All.
Require Import IoEffects.All.

Import ListNotations.
Import C.Notations.

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
| Print (message : LString.t)
(** Read a line on the standard input. *)
| ReadLine.

(** The type of an answer for a command depends on the value of the command. *)
Definition answer (command : t) : Type :=
  match command with
  | ListFiles _ => option (list LString.t)
  | ReadFile _ => option LString.t
  | WriteFile _ _ => bool
  | DeleteFile _ => bool
  | System _ => option bool
  | Print _ => bool
  | ReadLine => option LString.t
  end.

Definition effects : Effects.t := {|
  Effects.command := t;
  Effects.answer := answer |}.

Definition list_files (directory : LString.t)
  : C.t effects (option (list LString.t)) :=
  call effects (ListFiles directory).

Definition read_file (file_name : LString.t) : C.t effects (option LString.t) :=
  call effects (ReadFile file_name).

Definition write_file (file_name content : LString.t) : C.t effects bool :=
  call effects (WriteFile file_name content).

Definition delete_file (file_name : LString.t) : C.t effects bool :=
  call effects (DeleteFile file_name).

Definition system (command : LString.t) : C.t effects (option bool) :=
  call effects (System command).

Definition print (message : LString.t) : C.t effects bool :=
  call effects (Print message).

Definition printl (message : LString.t) : C.t effects bool :=
  call effects (Print (message ++ [LString.Char.n])).

Definition log (message : LString.t) : C.t effects unit :=
  do! printl message in
  ret tt.

Definition read_line : C.t effects (option LString.t) :=
  call effects ReadLine.

Module Run.
  Definition list_files_ok (directory : LString.t) (files : list LString.t)
    : Run.t (list_files directory) (Some files).
    apply (Run.Call effects (ListFiles directory)).
  Defined.

  Definition list_files_error (directory : LString.t)
    : Run.t (list_files directory) None.
    apply (Run.Call effects (ListFiles directory)).
  Defined.

  Definition read_file_ok (file_name : LString.t) (content : LString.t)
    : Run.t (read_file file_name) (Some content).
    apply (Run.Call effects (ReadFile file_name)).
  Defined.

  Definition read_file_error (file_name : LString.t)
    : Run.t (read_file file_name) None.
    apply (Run.Call effects (ReadFile file_name)).
  Defined.

  Definition write_file_ok (file_name content : LString.t)
    : Run.t (write_file file_name content) true.
    apply (Run.Call effects (WriteFile file_name content)).
  Defined.

  Definition write_file_error (file_name content : LString.t)
    : Run.t (write_file file_name content) false.
    apply (Run.Call effects (WriteFile file_name content)).
  Defined.

  Definition delete_file_ok (file_name : LString.t)
    : Run.t (delete_file file_name) true.
    apply (Run.Call effects (DeleteFile file_name)).
  Defined.

  Definition delete_file_error (file_name : LString.t)
    : Run.t (delete_file file_name) false.
    apply (Run.Call effects (DeleteFile file_name)).
  Defined.

  Definition system_ok (command : LString.t) (is_success : bool)
    : Run.t (system command) (Some is_success).
    apply (Run.Call effects (System command)).
  Defined.

  Definition system_error (command : LString.t) : Run.t (system command) None.
    apply (Run.Call effects (System command)).
  Defined.

  Definition print_ok (message : LString.t) : Run.t (print message) true.
    apply (Run.Call effects (Print message)).
  Defined.

  Definition print_error (message : LString.t) : Run.t (print message) false.
    apply (Run.Call effects (Print message)).
  Defined.

  Definition printl_ok (message : LString.t) : Run.t (printl message) true.
    apply (print_ok _).
  Defined.

  Definition printl_error (message : LString.t) : Run.t (printl message) false.
    apply (print_error _).
  Defined.

  Definition log_ok (message : LString.t) : Run.t (log message) tt.
    apply (Run.Let (printl_ok _)).
    apply Run.Ret.
  Defined.

  Definition read_line_ok (line : LString.t) : Run.t read_line (Some line).
    apply (Run.Call effects ReadLine (Some line)).
  Defined.

  Definition read_line_error : Run.t read_line None.
    apply (Run.Call effects ReadLine None).
  Defined.
End Run.
