(** Some OCaml primitives for the extraction. *)
open Big_int

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
    let buffer = String.create length in
    List.iteri (fun i c -> String.set buffer i c) s;
    buffer
end

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

(** Print a message on the standard output. *)
let print (message : string) : bool Lwt.t =
  Lwt.catch (fun _ ->
    Lwt.bind (Lwt_io.print message) (fun _ ->
    Lwt.return true))
    (fun _ -> Lwt.return false)
