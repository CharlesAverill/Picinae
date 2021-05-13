
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

(* If we have the instruction sequence 
  auipc r, #
  addi  r, r, # 
  that means the compiler is attempting to load a register with some address as an offset of the 
  program counter. as we are moving all the instructions, this relative offset will be incorrect.
  To rectify this, we will first calculate where the original address was attempting to jump. Then,
  knowing where that address was relative to the pc of that set of instructions, we can change the
  immediates to point to the original address
  *)
let rewrite_auipc_addi_block (input_list :int32 list) :int32 list = 
  []

(* given an output file, a "source" (a Bap.Std.Image) and a record, apply the patch and write it to the file and return unit*)
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
let prep_transform (input:(int * int list) * int list list option) = 
  let ((_, jumptable), suffix) = input in 
  let a = Stdlib.List.map Stdlib.Int32.of_int jumptable in
  let b = Stdlib.List.map Stdlib.Int32.of_int @@ Stdlib.List.concat @@ Stdlib.Option.get suffix in
  (a, b) 

(* Given a binary transformation function (from the extraction), a Bap.Std.Image, and an output file
  from Bap, do the transformat on the original image and write it out to the output file *)
exception NoTextSection of unit
exception NoE_Entry of unit
let rewrite image table_output text_output =
  match find_section image ".text" with
  | None -> raise (NoTextSection ())
  | Some section ->
    let int32_insns_list = (list_of_mem section) in
    let generated_policy = (Policy.generate_static_policy int32_insns_list) in
    let segment_addr = (Word.to_int_exn (Memory.min_addr section) ) in 
    let final_addr = (Bigstring.length (Image.data image)) in
    let insns_as_pure_int = (Stdlib.List.map Stdlib.Option.get ((Stdlib.List.map Stdlib.Int32.unsigned_to_int int32_insns_list))) in
    let offset_entry_point = (Stdlib.(/) (Stdlib.(-) (Word.to_int_exn (Image.entry_point image)) segment_addr) 4) in
    let generated_code = (Extraction.newcode 
      generated_policy 
      insns_as_pure_int
      segment_addr(*base *)
      final_addr(*base'*)
      offset_entry_point
    ) in 
    let ((new_entry_offset, _), generated_suffix) = generated_code in
    let new_entrypoint = (final_addr + (new_entry_offset* 4)) in
    (Format.printf "0x%x\n" new_entrypoint);
    let chunk1,suffix1 = prep_transform @@ generated_code in
    let table = bigstring_of_int32_list chunk1 in
    let text = bigstring_of_int32_list suffix1 in
    (write_bigstring ~output:table_output table);
    (write_bigstring ~output:text_output text);

