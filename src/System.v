Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ListString.All.
Require Import Io.All.

Import ListNotations.
Import C.Notations.

(** The System commands. *)
Inductive t :=
| ListFiles (directory : LString.t)
| ReadFile (file_name : LString.t)
| WriteFile (file_name : LString.t) (content : LString.t)
| DeleteFile (file_name : LString.t)
| System (command : LString.t)
| Eval (command : list LString.t)
| Print (message : LString.t)
| ReadLine.

(** The answers to System commands. *)
Definition answer (command : t) : Type :=
  match command with
  | ListFiles _ => option (list LString.t)
  | ReadFile _ => option LString.t
  | WriteFile _ _ => bool
  | DeleteFile _ => bool
  | System _ => option bool
  | Eval _ => option (Z * LString.t * LString.t)
  | Print _ => bool
  | ReadLine => option LString.t
  end.

(** The definition of the system effect. *)
Definition effect : Effect.t := {|
  Effect.command := t;
  Effect.answer := answer |}.

(** List the files of a directory. *)
Definition list_files (directory : LString.t)
  : C.t effect (option (list LString.t)) :=
  call effect (ListFiles directory).

(** Read the content of a file. *)
Definition read_file (file_name : LString.t) : C.t effect (option LString.t) :=
  call effect (ReadFile file_name).

(** Update (or create) a file with some content. *)
Definition write_file (file_name content : LString.t) : C.t effect bool :=
  call effect (WriteFile file_name content).

(** Delete a file. *)
Definition delete_file (file_name : LString.t) : C.t effect bool :=
  call effect (DeleteFile file_name).

(** Run a command. *)
Definition system (command : LString.t) : C.t effect (option bool) :=
  call effect (System command).

(** Run a command controlling the outputs. *)
Definition eval (command : list LString.t)
  : C.t effect (option (Z * LString.t * LString.t)) :=
  call effect (Eval command).

(** Print a message on the standard output. *)
Definition print (message : LString.t) : C.t effect bool :=
  call effect (Print message).

(** Print a message with an end of line on the standard output. *)
Definition printl (message : LString.t) : C.t effect bool :=
  call effect (Print (message ++ [LString.Char.n])).

(** Print a message with an end of line without checking the outcome. *)
Definition log (message : LString.t) : C.t effect unit :=
  let! is_success := printl message in
  ret tt.

(** Read a line on the standard input. *)
Definition read_line : C.t effect (option LString.t) :=
  call effect ReadLine.

(** Some basic scenarios. *)
Module Run.
  Import Io.Run.

  Definition list_files_ok (directory : LString.t) (files : list LString.t)
    : Run.t (list_files directory) (Some files).
    apply (Call (E := effect) (ListFiles directory)).
  Defined.

  Definition list_files_error (directory : LString.t)
    : Run.t (list_files directory) None.
    apply (Call (E := effect) (ListFiles directory)).
  Defined.

  Definition read_file_ok (file_name : LString.t) (content : LString.t)
    : Run.t (read_file file_name) (Some content).
    apply (Call (E := effect) (ReadFile file_name)).
  Defined.

  Definition read_file_error (file_name : LString.t)
    : Run.t (read_file file_name) None.
    apply (Call (E := effect) (ReadFile file_name)).
  Defined.

  Definition write_file_ok (file_name content : LString.t)
    : Run.t (write_file file_name content) true.
    apply (Call (E := effect) (WriteFile file_name content)).
  Defined.

  Definition write_file_error (file_name content : LString.t)
    : Run.t (write_file file_name content) false.
    apply (Call (E := effect) (WriteFile file_name content)).
  Defined.

  Definition delete_file_ok (file_name : LString.t)
    : Run.t (delete_file file_name) true.
    apply (Call (E := effect) (DeleteFile file_name)).
  Defined.

  Definition delete_file_error (file_name : LString.t)
    : Run.t (delete_file file_name) false.
    apply (Call (E := effect) (DeleteFile file_name)).
  Defined.

  Definition system_ok (command : LString.t) (is_success : bool)
    : Run.t (system command) (Some is_success).
    apply (Call (E := effect) (System command)).
  Defined.

  Definition system_error (command : LString.t) : Run.t (system command) None.
    apply (Call (E := effect) (System command)).
  Defined.

  Definition print_ok (message : LString.t) : Run.t (print message) true.
    apply (Call (E := effect) (Print message)).
  Defined.

  Definition print_error (message : LString.t) : Run.t (print message) false.
    apply (Call (E := effect) (Print message)).
  Defined.

  Definition printl_ok (message : LString.t) : Run.t (printl message) true.
    apply (print_ok _).
  Defined.

  Definition printl_error (message : LString.t) : Run.t (printl message) false.
    apply (print_error _).
  Defined.

  Definition log_ok (message : LString.t) : Run.t (log message) tt.
    apply (Let (printl_ok _)).
    apply Ret.
  Defined.

  Definition read_line_ok (line : LString.t) : Run.t read_line (Some line).
    apply (Call (E := effect) ReadLine (Some line)).
  Defined.

  Definition read_line_error : Run.t read_line None.
    apply (Call (E := effect) ReadLine None).
  Defined.
End Run.
