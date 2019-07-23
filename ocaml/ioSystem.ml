(** Some OCaml primitives for the extraction. *)
open Big_int

(** Interface to OCaml's big integers. *)
module Big = struct
  let rec to_positive_aux (big : big_int) xH xO xI =
    if eq_big_int big unit_big_int then
      xH
    else
      let big' = to_positive_aux (div_big_int big (big_int_of_int 2)) xH xO xI in
      if eq_big_int (mod_big_int big (big_int_of_int 2)) zero_big_int then
        xO big'
      else
        xI big'

  let to_Z_aux (big : big_int) z_O z_pos z_neg xH xO xI =
    if eq_big_int big zero_big_int then
      z_O
    else if gt_big_int big zero_big_int then
      z_pos (to_positive_aux big xH xO xI)
    else
      z_pos (to_positive_aux (minus_big_int big) xH xO xI)
end

(** Interface to the OCaml strings. *)
module String = struct
  (** Export an OCaml string. *)
  let to_lstring (s : string) : char list =
    let rec aux l i =
      if i = -1 then
        l
      else
        aux (s.[i] :: l) (i - 1) in
    aux [] (String.length s - 1)

  (** Import a Coq string. *)
  let of_lstring (s : char list) : string =
    let length = List.length s in
    let buffer = Bytes.create length in
    List.iteri (fun i c -> Bytes.set buffer i c) s;
    Bytes.to_string buffer
end

(** The command line arguments of the program. *)
let argv : string list =
  Array.to_list Sys.argv

(** Join. *)
let join (x : 'a Lwt.t) (y : 'b Lwt.t) : ('a * 'b) Lwt.t =
  let r_x = ref None in
  let r_y = ref None in
  Lwt.bind (Lwt.join [
    Lwt.bind x (fun x -> r_x := Some x; Lwt.return ());
    Lwt.bind y (fun y -> r_y := Some y; Lwt.return ())])
    (fun (_ : unit) ->
      match (!r_x, !r_y) with
      | (Some x, Some y) -> Lwt.return (x, y)
      | _ -> Lwt.fail_with "The join expected two answers.")

(** Choose. *)
let choose (x1 : 'a Lwt.t) (x2 : 'a Lwt.t) : 'a Lwt.t =
  Lwt.pick [x1; x2]

(** List the files of a directory. *)
let list_files (directory : string) : string list option Lwt.t =
  Lwt.catch (fun _ ->
    let file_names = Lwt_unix.files_of_directory directory in
    Lwt.bind (Lwt_stream.to_list file_names) (fun file_names ->
    Lwt.return @@ Some file_names))
    (fun _ -> Lwt.return None)

(** Read the content of a file. *)
let read_file (file_name : string) : string option Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.open_file Lwt_io.Input file_name) (fun channel ->
    Lwt.bind (Lwt_io.read channel) (fun content ->
    Lwt.bind (Lwt_io.close channel) (fun _ ->
    Lwt.return @@ Some content))))
    (fun _ -> Lwt.return None)

(** Update (or create) a file with some content. *)
let write_file (file_name : string) (content : string) : bool Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.open_file Lwt_io.Output file_name) (fun channel ->
    Lwt.bind (Lwt_io.write channel content) (fun content ->
    Lwt.bind (Lwt_io.close channel) (fun _ ->
    Lwt.return true))))
    (fun _ -> Lwt.return false)

(** Delete a file. *)
let delete_file (file_name : string) : bool Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_unix.unlink file_name) (fun _ ->
    Lwt.return true))
    (fun _ -> Lwt.return false)

(** Run a command. *)
let system (command : string) : bool option Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_unix.system command) (fun status ->
    Lwt.return @@ Some (match status with
    | Lwt_unix.WEXITED 0 | Lwt_unix.WSIGNALED 0 | Lwt_unix.WSTOPPED 0 -> true
    | Lwt_unix.WEXITED _ | Lwt_unix.WSIGNALED _ | Lwt_unix.WSTOPPED _ -> false)))
    (fun _ -> Lwt.return None)

(** Run a command controlling the outputs. *)
let eval (command : string list) : ((big_int * string) * string) option Lwt.t =
  Lwt.catch (fun _ ->
    let command = Array.of_list command in
    Lwt_process.with_process_full ("", command) (fun process ->
    Lwt.bind (process#status) (fun (status : Unix.process_status) ->
    Lwt.bind (Lwt_io.read process#stdout) (fun (output : string) ->
    Lwt.bind (Lwt_io.read process#stderr) (fun (error : string) ->
    Lwt.bind (Lwt.join [
      Lwt_io.close process#stdin;
      Lwt_io.close process#stdout;
      Lwt_io.close process#stderr]) (fun (_ : unit) ->
    let status = match status with
      | Unix.WEXITED n | Unix.WSIGNALED n | Unix.WSTOPPED n -> n in
    Lwt.return @@ Some ((big_int_of_int status, output), error)))))))
    (fun _ -> Lwt.return None)

(** Print a message on the standard output. *)
let print (message : string) : bool Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.print message) (fun _ ->
    Lwt.return true))
    (fun _ -> Lwt.return false)

(** Read a line on the standard input. *)
let read_line () : string option Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.read_line Lwt_io.stdin) (fun line ->
    Lwt.return (Some line)))
    (fun _ -> Lwt.return None)
