
open Core_kernel
open Bap.Std
open Bap_main

module Unix = UnixLabels

(* a "chunk" defines an offset (in number of bytes from the start of the file) 
  and a Core_kernel.Bigstring.t that efficiently represents the data for that "chunk",
  which in this case is analogus to an ELF binary "section" *)
type chunk = {
  offset : int;
  data: Bigstring.t
}

type patch = {
  chunks: chunk list;
  suffix: Bigstring.t;
}

(* Given a Bap.Std.Memory, find its offset from the start of the file *)
let offset mem =
  Bigsubstring.pos (Memory.to_buffer mem)

(* Given a Bap.Std.Image and a string that is the name of a symbol, return an
  option of that symbol*)
let find_symbol image name =
  Image.memory image |>  (* Get a Memmap from the image *)
  Memmap.to_sequence |>  (* Get a Sequence from said image *)
  Seq.find_map ~f:(fun (data, annotation) -> (* iterate and return an option for the thing we want *)
    match Value.get Image.symbol annotation with
    | None -> None
    | Some section -> Option.some_if (String.equal section name) data)

(* Given a Bap.Std.Image and a string that is the name of an ELF section, return an
  option of that section *)
let find_section image name =
  Image.memory image |>  (* Get a Memmap from the image *)
  Memmap.to_sequence |>  (* Get a Sequence from said image *)
  Seq.find_map ~f:(fun (data, annotation) -> (* iterate and return an option for the thing we want *)
    match Value.get Image.section annotation with
    | None -> None
    | Some section -> Option.some_if (String.equal section name) data)

(* given a Bap.Std.Memory, assume it is a list of 32 bit integers and return it as such. *)
let list_of_mem (mem :Memory.t) : (int32 list) =
  List.rev @@
  Memory.fold mem ~word_size:`r32 ~init:[] ~f:(fun w ws ->
      Word.to_int32_exn w :: ws)

(* use memory mapping to map a file to a Bigarray.t *)
let mapfile fd size =
  Bigarray.array1_of_genarray @@ (Unix.map_file fd
    ~pos:0L
    ~kind:Bigarray.char
    ~layout:Bigarray.c_layout
    ~shared:true
    ~dims:([|size |]))

(* given a list of int32 values, create a Bigstring.t that holds those values, sequentially *)
let bigstring_of_int32_list input_list =
  let size = (List.length input_list) * 4 in (* multiply by 4 to get number of bytes, not instructions *)
  let destination = Bigstring.create size in
  List.iteri input_list ~f:(fun i x ->
    (* iteratively set the values in the Bigstring we allocated from the values in the input_list *)
    Bigstring.set_int32_t_le destination ~pos:(i*4) x); (* semicolon operator to return value *)
  destination (* return the now-filled destination *)

(* given an output file, a "source" (a Bap.Std.Image) and a record, apply the
   patch and write it to the file and return unit*)
let apply_patch ~output source new_entrypoint mypatch =
  let {chunks; suffix} = mypatch in
  let fd = Unix.openfile output
    ~mode:Unix.[O_RDWR; O_CREAT]
    ~perm:0o600 in
  (* The size of the new file, with suffix *)
  let size = Bigstring.length source + Bigstring.length suffix in
  (* the contents of the output file, memory mapped *)
  let destination = mapfile fd size in
  (* Set the entry point as the 24th byte in the file (the offset of `e_entry` in the ELF header) *)
  (Bigstring.set_int32_t_le source ~pos:24 new_entrypoint);
  (* Blit the input data *)
  Bigstring.blito ~src:source ~dst:destination ();
  (* append the suffix *)
  (Format.printf "The output number is %d\n" (Bigstring.length source));
  Bigstring.blito ~src:suffix ~dst:destination ~dst_pos:(Bigstring.length source) ();
  (* For each chunk, blit it to the output. these are the overwritten chunks *)
  List.iter chunks ~f:(fun chunk ->
    let {offset; data} = chunk in
    Bigstring.blito ~src:data ~dst:destination ~dst_pos:offset ()
  );
  Unix.close fd

let write_bigstring ~output bigstring_source =
  let fd = Unix.openfile output
    ~mode:Unix.[O_RDWR; O_CREAT]
    ~perm:0o600 in
  (* The size of the new file, with suffix *)
  let size = Bigstring.length bigstring_source in
  (* the contents of the output file, memory mapped *)
  let destination = mapfile fd size in
  (* Blit the input data *)
  Bigstring.blito ~src:bigstring_source ~dst:destination ()

(* given the return of a call to Extraction.newcode, produce an int32 list * int32 list *)
let prep_transform (input:int list * int list list option) =
  let open Result.Let_syntax in
  let (jumptable, suffix) = input in
  let%bind insns = Result.of_option ~error:(Error.of_string
    "Unable to transform code due to some illegal jumps") suffix in
  let convNumb lst = Result.of_option ~error:(Error.of_string
    "Overflowing integer") @@ Option.all @@ List.map ~f:Int32.of_int lst in
  let%bind a = convNumb jumptable in
  let%map  b = convNumb @@ List.concat insns in
  (a, b)

(* Given a binary transformation function (from the extraction), a Bap.Std.Image, and an output file
  from Bap, do the transformat on the original image and write it out to the output file *)
let rewrite image table_output text_output =
  let open Result.Let_syntax in
  let%bind section = Result.of_option ~error:(Error.of_string
    "Cannot find text section") @@ find_section image ".text" in
  let insns_int32 = list_of_mem section in
  let generated_policy = Policy.generate_static_policy insns_int32 in
  let segment_addr = Word.to_int_exn @@ Memory.min_addr section in
  let final_addr = Bigstring.length @@ Image.data image in
  (* Note that to_int_exn should never throw in 64-bit mode *)
  let insns_int = List.map ~f:Int32.to_int_exn insns_int32 in
  let offset_entry_point = Int.shift_right
    ((Word.to_int_exn @@ Image.entry_point image) - segment_addr) 2 in
  let new_entry_offset = Extraction.mapaddr generated_policy insns_int
        offset_entry_point in
  let new_entrypoint = final_addr + new_entry_offset * 4 in
  let generated_code = (Extraction.newcode
    generated_policy
    insns_int
    segment_addr(*base *)
    final_addr(*base'*)
  ) in
  let%map chunk1,suffix1 = prep_transform @@ generated_code in
  let table = bigstring_of_int32_list chunk1 in
  let text = bigstring_of_int32_list suffix1 in
  (write_bigstring ~output:table_output table);
  (write_bigstring ~output:text_output text);
(* TODO: do some rewriting into a custom binary *)
