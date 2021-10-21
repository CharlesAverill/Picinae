
open Bap.Std
open Bap_main
open Bap_elf.Std.Elf
open Core_extend
open Elf_write
open Elf_segments

module Unix = UnixLabels

(* given a list of int32 values, create a Bigstring.t that holds those values,
   sequentially *)

type policy = (int option * (int * int list)) list
  [@@deriving sexp]

let bigstring_of_int32_list input_list =
  let size = (List.length input_list) * 4 in (* multiply by 4 to get number of bytes, not instructions *)
  let destination = Bigstring.create size in
  List.iteri input_list ~f:(fun i x ->
    (* iteratively set the values in the Bigstring we allocated from the values in the input_list *)
    Bigstring.set_int32_t_le destination ~pos:(i*4) x); (* semicolon operator to return value *)
  destination (* return the now-filled destination *)

(* given the return of a call to Extraction.newcode, produce an int32 list
 * int32 list *)
let prep_transform (input:int list * int list list option) =
  let open Result.Let_syntax in
  let (jumptable, suffix) = input in
  let%map insns = Result.of_option ~error:(Error.of_string
    "Unable to transform code.") suffix in
  let convNumb lst = List.map ~f:Int32.of_int_trunc lst in
  let a = convNumb jumptable in
  let b = convNumb @@ List.concat insns in
  (a, b)


(* Rewrites the binary pointed by this elf image object and adds the rewritten
   code back in as a brand-new code segment *)
let spacer_size = 0x10000
let mask_int32 = 0xFFFFFFFFL
let rewrite image mapfile abort_handler =
  let () = debugf "Loaded image" in
  let open Result.Let_syntax in
  (* We assume that all code sections and ONLY code sections are marked as
     executable and that they are contiguous. With that in mind, we need to
     gather the base address of the code section, and the size of this
     code section. *)
  let%bind (mcode_base, code_size) =
    image.i_elf.elf_.e_sections |>
    Sequence.filter ~f:(fun sect -> Option.is_some @@
      List.locate SHF_EXECINSTR sect.sh_flags &&
      phys_equal sect.sh_type SHT_PROGBITS) |>
    Sequence.to_list |>
    List.sort_on ~f:sh_addr ~cmp:Int64.compare |>
    List.fold_result ~init:(None, 0L) ~f:(fun (mbase, size) sect ->
      Option.inject mbase ~def:(Ok (Some sect.sh_addr, sect.sh_size))
        ~f:(fun base ->
          let open Int64 in
          let%map _ = Result.of_option
            ~error:(fail "Not contiguous code sections") @@
            Option.guard (base + size = sect.sh_addr) in
          (Some base, size + sect.sh_size))) in
  let%bind code_base = Result.of_option
    ~error:(fail "No code sections found") mcode_base in
  let () = debugf "Found code base at: %016Lx +%08Lx" code_base code_size in

  let%bind code_mem_r = mem_of_address image code_base code_size >>| Memory.read in
  let () = debugf "Reading %d instructions" (Bigstring.length code_mem_r / 4) in
  let%bind insns = Result.all @@
    List.init ~f:(fun pos ->
      Int64.to_int_err @@ Int64.bit_and mask_int32 @@ Int64.of_int32 @@
      Bigstring.get_int32_t_le ~pos:(pos * 4) code_mem_r) @@
    Bigstring.length code_mem_r / 4 in
  let () = debugf "Loaded instructions" in

  (* Create a code spacer *)
  let%bind (image, segm_spacer, _) = Elf_segments.new_segment
    ~p_flags:[] ~filesz:0 ~memsz:spacer_size image AnySpec in

  (* Parameters for newcode *)
  let generated_policy = Policy.generate_static_policy insns in
  let open Int64 in
  let%bind orig_addr = to_int_err code_base in
  let%bind final_addr = to_int_err @@ align_up ~align:page_align @@
    segm_spacer.p_vaddr + segm_spacer.p_memsz in
  let%bind entrypoint = to_int_err image.i_elf.elf_.e_entry in
  let new_entrypoint = Int.(Extraction.mapaddr generated_policy insns
    (shift_right (entrypoint - orig_addr) 2) * 4 + final_addr) in
  let image = {image with i_elf = {image.i_elf with elf_ = {
    image.i_elf.elf_ with e_entry = of_int new_entrypoint
  }}} in

  (* Calling rewriting*)
  let () = debugf "Rewriting instructions..." in
  let (newtable, mnewcode) = Extraction.newcode generated_policy insns
    Int.(orig_addr/4) Int.(final_addr/4) in
  let () = debugf "Code rewritten" in
  let%bind newcode = Result.of_option ~error:(Error.of_string
    "Unable to transform code.") mnewcode in
  let newtable_data = bigstring_of_int32_list @@
    List.map ~f:Int32.of_int_trunc newtable in
  let newcode_data = bigstring_of_int32_list @@
    List.map ~f:Int32.of_int_trunc @@
    List.concat @@
    List.append newcode [abort_handler] in

  (* Write new code back into the image *)
  let%bind (image, new_segm, _) = Elf_segments.new_segment
    ~content:newcode_data ~p_flags:[PF_R; PF_X]
    image (AddressOnlySpec (Int64.of_int final_addr)) in
  let%bind code_mem = mem_of_address image code_base code_size in
  let%map () = Memory.write code_mem newtable_data in
  let () = debugf "Rewritten back into image" in

  (* Write map file if needed *)
  let () = Option.inject mapfile ~def:() ~f:(fun mapfile ->
    (* Open the map file*)
    let fd = Unix.openfile mapfile
      ~mode:[Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC]
      ~perm:0o644 in
    let out = Unix.out_channel_of_descr fd in

    (* For each instruction, compute the mapping *)
    let (_, _) = List.fold_left newcode ~init:(code_base, new_segm.p_vaddr)
      ~f:(fun (oldbase, newbase) insns ->
        let () = fprintf out "0x%08Lx: 0x%08Lx\n" oldbase newbase in
        (oldbase + 4L, newbase + 4L * (Int64.of_int @@ List.length insns))) in

    (* Close the file *)
    let () = Out_channel.close out in
    let () = debugf "Written map file" in ()) in
  image
