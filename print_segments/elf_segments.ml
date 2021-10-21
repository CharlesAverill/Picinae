open Core_extend
open Bap_elf.Std.Elf
open Bap.Std

module Unix = UnixLabels

type segments =
  { s_heads: segment list;
    s_loads_by_vaddr: (int64, segment, Int64.comparator_witness) Map.t;
    s_others: segment list;
  }

type image =
  { i_fd:   Unix.file_descr;
    i_mem:  Bigstring.t;
    i_elf:  Elf_write.elf2;
    i_segs: segments;
    i_phdr_cap: int64;
  }

let elf_max_header_size = 64
let phdr_align   = 8L
let offset_align = 0x10L
let page_align   = 0x1000L
let min_phdr_expand = 0x300L

let nil = Bigstring.create 0

let s_loads segs = List.map ~f:snd (Map.to_alist segs.s_loads_by_vaddr)

let update_load_seg segs new_seg = { segs with
  s_loads_by_vaddr = Map.set segs.s_loads_by_vaddr
    ~key:new_seg.p_vaddr ~data:new_seg;
}

let get_top_offset image =
  let open Int64 in
  let elf = image.i_elf in
  let top_seg_offset =
    Map.fold ~init:0L ~f:(fun ~key ~data cur_off ->
      let new_off = align_up ~align:offset_align @@
        data.p_offset + data.p_filesz in
      if new_off > cur_off then new_off else cur_off)
      image.i_segs.s_loads_by_vaddr in
  let top_sect_offset =
    Sequence.fold ~init:0L ~f:(fun cur_off sect ->
      let new_off = align_up ~align:offset_align @@
        sect.sh_offset + sect.sh_size in
      if new_off > cur_off then new_off else cur_off)
      elf.elf_.e_sections in
  let segms = Int64.of_int @@ Sequence.length elf.elf_.e_segments in
  let sects = Int64.of_int @@ Sequence.length elf.elf_.e_sections in
  max top_sect_offset @@ max top_seg_offset @@
  max (elf.e_phoff + elf.e_phentsize * segms) (elf.e_shoff + elf.e_shentsize * sects)

let segments_size segs = List.length segs.s_heads +
  Map.length segs.s_loads_by_vaddr + List.length segs.s_others
let flatten_segments segs = segs.s_heads @ s_loads segs @ segs.s_others

let seg_olap_vaddr prev cur = let open Int64 in
  prev.p_vaddr + prev.p_memsz > cur.p_vaddr

let mapfile fd ~size ~shared =
  Bigarray.array1_of_genarray @@ (Unix.map_file fd
    ~pos:0L
    ~kind:Bigarray.char
    ~layout:Bigarray.c_layout
    ~shared:shared
    ~dims:([|size |]))

let bitstring_of_bytes b = b, 0, Bytes.length b * 8

module Memory = struct
  type t = Bigstring.t list

  let singleton bs = [bs]

  let length = List.sum (module Int) ~f:Bigstring.length

  let read mem = Bigstring.concat mem

  let write ?(src_pos=0) ?(dst_pos=0) mem src =
    let open Result.Let_syntax in
    (* Do bounds check of the src_pos and dst_pos *)
    let%bind _ = Result.of_option
      ~error:(failf "Illegal src_pos (%d)" src_pos) @@
      Option.guard (src_pos <= Bigstring.length src) in
    let%map _ = Result.of_option
      ~error:(failf "Illegal dst_pos (%d)" dst_pos) @@
      Option.guard (dst_pos + (Bigstring.length src - src_pos) <=
        length mem) in
    (* Do the actual copying *)
    List.fold_until mem
      ~init:(src_pos, dst_pos)
      ~finish:ignore
      ~f:(fun (src_pos, dst_pos) dstmem ->
        let open Continue_or_stop.Let_syntax in
        (* Break if src_pos reaches end *)
        let%bind _ = Continue_or_stop.guard ~stop:()
          (src_pos < Bigstring.length src) in
        (* Otherwise, write into the segment *)
        if dst_pos >= Bigstring.length dstmem
        then return (src_pos, dst_pos - Bigstring.length dstmem)
        else
          let len = min (Bigstring.length src - src_pos)
            (Bigstring.length dstmem - dst_pos) in
          Bigstring.blit ~src ~src_pos ~dst:dstmem ~dst_pos ~len;
          return (src_pos + len, 0))
end

let save_image image path =
  let fd = Unix.openfile path
    ~mode:[Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC]
    ~perm:0o755 in
  let outmem = mapfile fd ~shared:true ~size:(Bigstring.length image.i_mem) in
  Bigstring.blito ~src:image.i_mem ~dst:outmem ();
  Unix.close fd

let load_image path =
  let fd = Unix.openfile path ~mode:[Unix.O_RDONLY] ~perm:0 in
  let mem = mapfile fd ~shared:false ~size:(Unix.fstat fd).st_size in
  let header = Bytes.create elf_max_header_size in
  Bigstring.To_bytes.blito ~src:mem ~dst:header
    ~src_len:(min (Bigstring.length mem) elf_max_header_size) ();
  let open Result.Let_syntax in
  let%bind elf = from_bigstring mem in
  let%bind elf2 = Elf_write.extend_elf_hdr elf @@ bitstring_of_bytes header in
  let (_, heads, loads, others, ents) = Sequence.fold
    ~init:(true, [], [], [], 0)
    ~f:(fun (in_head, heads, loads, others, ents) segm ->
      match segm.p_type with
      | PT_LOAD -> (false, heads, segm :: loads, others, ents + 1)
      | _ ->
          if in_head
          then (true, segm :: heads, loads, others, ents + 1)
          else (false, heads, loads, segm :: others, ents + 1)) elf.e_segments in
  let loads_sorted_vaddr = List.sort_on ~cmp:Int64.compare ~f:p_vaddr loads in
  let has_pairing fn lst = snd @@ List.fold_left ~init:(None, false)
      ~f:(fun (mprev, pred) cur -> (Some cur, Option.inject mprev ~def:pred
        ~f:(fun prev -> pred || fn prev cur))) lst in
  let open Int64 in
  let overlapping_vaddr = has_pairing seg_olap_vaddr loads_sorted_vaddr in
  let%bind _ = Result.of_option
    ~error:(fail "Overlapping LOAD segments") @@
    Option.guard @@ not overlapping_vaddr in
  let%bind loads_offset = Map.of_alist_or_error @@ List.map ~f:(fun seg ->
      (seg.p_offset, seg)) loads in
  let%map loads_vaddr = Map.of_alist_or_error @@ List.map ~f:(fun seg ->
      (seg.p_vaddr, seg)) loads in
  let segs = {
    s_heads = List.rev heads;
    s_loads_by_vaddr = loads_vaddr;
    s_others = List.rev others;
  } in {
    i_fd   = fd;
    i_mem  = mem;
    i_elf  = elf2;
    i_segs = segs;
    i_phdr_cap = Int64.of_int ents;
  }

let save_image_hdrs image =
  let open Result.Let_syntax in
  let%bind _ = Elf_write.write_elf_ehdr image.i_elf image.i_mem in
  let%bind _ = Elf_write.write_elf_phdr image.i_elf image.i_mem in
               Elf_write.write_elf_shdr image.i_elf image.i_mem

let ensure_mem_size image memsize' =
  let old_size = Bigstring.length image.i_mem in
  let memsize = Int64.to_int_trunc memsize' in
  if old_size < memsize
  then
    let enlarge = (memsize - old_size + 0x2000) in
    let tmp = Bigstring.make enlarge '\x00' in
    let mem' = Bigstring.concat [image.i_mem; tmp] in
    {image with i_mem = mem'}
  else image

(* First thing we need to do in order to be able to add some number of new elf
   segments is being able to relocate the program header table. We have
   multiple strategies for doing so:

   1. Extending beyond some already existing segment

   2. Extending the final segment

   3. Creating a new segment

*)

(* This strategy for program header resizing utilizes an existing program
   segment, i.e. the unused space between two program segments. This works
   because program segments all must be aligned by page boundaries, leaving lots
   of unusable memory both in the file and in the memory map.

   It extends some program segment, which must its offset from the beginning of
   the file be equal to the address distance from the first LOAD segment, due to
   a quirk in how the loader/kernel loads the PHDR.
*)
type finding =
  { f_largest_unused_space: int64;
    f_res:     segment option;
    f_prevseg: segment;
  }

let resize_phdr_table_extend_unused image min_phdr_size =
  let open Int64 in
  match s_loads image.i_segs with
  | [] -> None
  | first_seg::rem_segs ->
      let open Option.Let_syntax in
      let res = List.fold_left
        ~init:{
          f_largest_unused_space = 0L;
          f_res = None;
          f_prevseg = first_seg;
        }
        ~f:(fun acc seg ->
          let seg_end_poff = acc.f_prevseg.p_offset + acc.f_prevseg.p_memsz in
          (* We assume that p_vaddr = p_paddr for all program segments *)
          let seg_end_vaddr = acc.f_prevseg.p_vaddr + acc.f_prevseg.p_memsz in
          let cur_unused_space = min (seg.p_offset - seg_end_poff)
            (align_down ~align:seg.p_align seg.p_vaddr - seg_end_vaddr) in

          (* Check if this satisfies the check of being the correct offset
           * away from the first loaded LOAD segment (due to some weirdness
           * in the loader/kernel, the kernel believes the PHDR entry in
           * memory as the FIRST_LOAD_SEGMENT + e_phoff, rather than using
           * the PHDR entry).
           *
           * For now we also need filesz == memsz too!
           *
           * TODO: check if any section header data also overlap here too! *)
          let is_viable_for_phdr = equal (seg_end_poff - first_seg.p_offset)
            (seg_end_vaddr - first_seg.p_vaddr) &&
            equal (acc.f_prevseg.p_memsz) (acc.f_prevseg.p_filesz) in
          if is_viable_for_phdr && (cur_unused_space >
            acc.f_largest_unused_space)
          then {
            f_largest_unused_space = cur_unused_space;
            f_res = Some acc.f_prevseg;
            f_prevseg = seg;
          }
          else {
            f_largest_unused_space = acc.f_largest_unused_space;
            f_res = acc.f_res;
            f_prevseg = seg;
          })
        rem_segs in
      let%bind seg = res.f_res in
      let%map _ = Option.guard (res.f_largest_unused_space >= min_phdr_size) in
      let new_seg_sz = seg.p_memsz + res.f_largest_unused_space in
      let phdr_virt_addr = align_up ~align:phdr_align @@
        seg.p_vaddr + seg.p_memsz in
      (* Assumes that address + offset of first segment is aligned same way *)
      let phdr_offset = align_up ~align:phdr_align @@
        seg.p_offset + seg.p_memsz in
      let seg_ext = { seg with
        p_memsz  = new_seg_sz;
        p_filesz = new_seg_sz;
      } in
      let new_phdr_ent = {
        p_type   = PT_PHDR;
        p_offset = phdr_offset;
        p_flags  = [PF_R];
        p_memsz  = res.f_largest_unused_space;
        p_filesz = res.f_largest_unused_space;
        p_vaddr  = phdr_virt_addr;
        p_paddr  = phdr_virt_addr;
        p_align  = phdr_align;
      } in
      let new_segs = update_load_seg image.i_segs seg_ext in
      let () = debugf "Resizing PHDR using 'extend unused' method" in
      (new_segs, new_phdr_ent)

(* This strategy for program header resizing extends the last program segment.
   As noted in previous strategy, the segment's offset from the beginning of
   the file be equal to the address distance from the first LOAD segment.

   TODO: we should try to check where phdr is already and maybe extend that one
   if we can!
*)
let resize_phdr_table_extend_last image min_phdr_size =
  let open Option.Let_syntax in
  let open Int64 in
  let%bind (_, first_seg) = Map.min_elt image.i_segs.s_loads_by_vaddr in
  let%bind (_, last_seg)  = Map.max_elt image.i_segs.s_loads_by_vaddr in
  let%bind _ = Option.guard ((last_seg.p_offset - first_seg.p_offset) =
    (last_seg.p_vaddr - first_seg.p_vaddr)) in
  (* TODO: maybe try to make this more efficient? *)
  let%map _ = Option.guard @@
    equal (last_seg.p_memsz) (last_seg.p_filesz) in
  let new_seg_sz = last_seg.p_memsz + min_phdr_size in
  let seg_ext = { last_seg with
    p_memsz  = new_seg_sz;
    p_filesz = new_seg_sz;
  } in
  let phdr_virt_addr = align_up ~align:phdr_align @@
    last_seg.p_vaddr + last_seg.p_memsz in
  let phdr_offset = align_up ~align:phdr_align @@
    last_seg.p_offset + last_seg.p_memsz in
  let new_phdr_ent = {
    p_type   = PT_PHDR;
    p_offset = phdr_offset;
    p_flags  = [PF_R];
    p_memsz  = min_phdr_size;
    p_filesz = min_phdr_size;
    p_vaddr  = phdr_virt_addr;
    p_paddr  = phdr_virt_addr;
    p_align  = phdr_align;
  } in
  let new_segs = update_load_seg image.i_segs seg_ext in
  let () = debugf "Resizing PHDR using 'extend last' method" in
  (new_segs, new_phdr_ent)

(* This strategy for program header resizing creates a new segment and uses that
   to allocate for PHDR. This is the least efficient way to do so. *)

(* TODO: need to implement this! *)
let resize_phdr_table_create image min_phdr_size =
  let open Option.Let_syntax in
  let open Int64 in
  let%bind (_, top_vaddr_seg) = Map.max_elt image.i_segs.s_loads_by_vaddr in
  let%map (_, bot_vaddr_seg) = Map.min_elt image.i_segs.s_loads_by_vaddr in
  let top_offset = get_top_offset image in
  let bot_vaddr = align_down ~align:page_align bot_vaddr_seg.p_vaddr in
  let top_vaddr = align_up ~align:page_align
    (top_vaddr_seg.p_vaddr + top_vaddr_seg.p_memsz) in

  let phdr_offset = align_up ~align:page_align @@
    max (top_vaddr - bot_vaddr) (top_offset) in
  let phdr_virt_addr = bot_vaddr + phdr_offset in
  let phdr_size = align_up ~align:page_align min_phdr_size in
  let new_phdr_ent = {
    p_type   = PT_PHDR;
    p_offset = phdr_offset;
    p_flags  = [PF_R];
    p_memsz  = phdr_size;
    p_filesz = phdr_size;
    p_vaddr  = phdr_virt_addr;
    p_paddr  = phdr_virt_addr;
    p_align  = phdr_align;
  } in
  let new_phdr_load_ent = {
    p_type   = PT_LOAD;
    p_offset = phdr_offset;
    p_flags  = [PF_R];
    p_memsz  = phdr_size;
    p_filesz = phdr_size;
    p_vaddr  = phdr_virt_addr;
    p_paddr  = phdr_virt_addr;
    p_align  = page_align;
  } in
  let new_segs = update_load_seg image.i_segs new_phdr_load_ent in
  let () = debugf "Resizing PHDR using 'create' method" in
  (new_segs, new_phdr_ent)


(* Fix any PT_PHDR program entries to point to a new PHDR location *)
let fix_phdr_entry segs phdr_ent =
  let fix_segs = List.map ~f:(fun seg -> match seg.p_type with
    | PT_PHDR -> phdr_ent
    | _ -> seg) in
  {
    s_heads = fix_segs segs.s_heads;
    s_loads_by_vaddr  = segs.s_loads_by_vaddr;
    s_others = fix_segs segs.s_others;
  }

let resize_strategies =
  [resize_phdr_table_extend_unused;
   resize_phdr_table_extend_last;
   resize_phdr_table_create;
  ]

(* Update the PHDR table with a set of new program segments *)
let update_phdr_table image new_segs =
  let open Result.Let_syntax in
  let image' = { image with
    i_elf = { image.i_elf with
      elf_ = { image.i_elf.elf_ with
        e_segments = Sequence.of_list @@ flatten_segments new_segs;
      };
    };
    i_segs = new_segs;
  } in
  let%map _ = save_image_hdrs image' in
  image'

(* Actual resize phdr function *)
let resize_phdr_table ?(need_phdr_entries = 1L) image =
  let open Result.Let_syntax in
  let open Int64 in
  let min_phdr_size = max min_phdr_expand
    ((need_phdr_entries + image.i_phdr_cap) * 2L * image.i_elf.e_phentsize) in
  let%bind (new_segs, phdr_ent) = Result.of_option
    ~error:(fail "No available strategies for resizing PHDR table") @@
    List.find_map ~f:(fun strategy -> strategy image min_phdr_size)
    resize_strategies in
  let new_segs = fix_phdr_entry new_segs phdr_ent in
  let image = { image with
    i_elf = { image.i_elf with
      e_phoff = phdr_ent.p_offset;
    };
    i_phdr_cap = phdr_ent.p_filesz / image.i_elf.e_phentsize;
  } in
  let image = ensure_mem_size image (phdr_ent.p_offset + phdr_ent.p_filesz) in
  update_phdr_table image new_segs

(* Ensure we can insert some number of program header entries into the PHDR. *)
let ensure_phdr_cap ?(insert_cnt = 1) image =
  let need_cap = Int64.of_int @@ insert_cnt + segments_size image.i_segs in
  let open Int64 in
  let open Result.Let_syntax in
  if image.i_phdr_cap < need_cap
  then
    resize_phdr_table
      ~need_phdr_entries:(need_cap - image.i_phdr_cap) image
  else Result.Ok image


let mem_of_address image addr size =
  let rec helper addr size acc =
    let open Int64 in
    if size = 0L then Result.Ok acc else
      let open Result.Let_syntax in
      let err_ill_mem = fail @@ Printf.sprintf
        "Illegal memory access (0x%016Lx)." addr in
      let%bind (_, seg) = Result.of_option ~error:err_ill_mem @@
        Map.closest_key image.i_segs.s_loads_by_vaddr `Less_or_equal_to addr in
      let%bind _ = Result.of_option ~error:err_ill_mem @@
        Option.guard (seg.p_vaddr + seg.p_memsz > addr) in
      let seg_offset = addr - seg.p_vaddr in
      let%bind (buff, sz_i) = if seg.p_vaddr + seg.p_filesz <= addr
        (* Return a memory of null bytes *)
        then
          let%map sz = to_int_err @@ min size @@ seg.p_memsz - seg_offset in
          (Bigstring.make sz '\x00', sz)
        else
          let%bind sz = to_int_err @@ min size @@ seg.p_filesz - seg_offset in
          let%map off = to_int_err @@ seg_offset + seg.p_offset in
          let bs = Bigstring.sub_shared image.i_mem
            ~pos:off ~len:sz in
          (bs, sz) in
      let sz = of_int sz_i in
      helper (addr + sz) (size - sz) (buff :: acc)
  in Result.map ~f:List.rev @@ helper addr size []

let mem_of_offset image offset size =
  let open Result.Let_syntax in
  let%bind offset_i = Int64.to_int_err offset in
  let%map size_i = Int64.to_int_err size in
  Memory.singleton @@
    Bigstring.sub_shared ~pos:offset_i ~len:size_i image.i_mem

let mem_of_segment image segm =
  mem_of_offset image segm.p_offset segm.p_filesz

type address_spec =
  | OffsetAddressSpec of (int64 * int64)
  | AddressOnlySpec   of int64
  | OffsetOnlySpec    of int64
  | AnySpec

(* This creates a new program segment of some size that can be written to  *)
let new_segment ?(content = nil) ?(p_flags = [PF_R; PF_W; PF_X])
  ?(p_type = PT_LOAD) ?filesz ?memsz ?(p_align = 0x1000L) image addr_spec =
    let p_filesz = Int64.of_int @@ Option.inject filesz
      ~def:(Bigstring.length content + 0x10) ~f:ident in
    let p_memsz = Option.inject ~def:p_filesz ~f:Int64.of_int memsz in
    let open Result.Let_syntax in
    let open Int64 in
    (* Fix PHDR as needed *)
    let%bind image = ensure_phdr_cap image in

    (* Compute the top offsets/ addresses *)
    let%bind (_, top_vaddr_seg) = Result.of_option
      ~error:(fail "No LOAD segments") @@
      Map.max_elt image.i_segs.s_loads_by_vaddr in
    let top_offset = if p_filesz = 0L then 0L else get_top_offset image in
    let top_vaddr = align_up ~align:page_align
      (top_vaddr_seg.p_vaddr + top_vaddr_seg.p_memsz) in
    let page_offset = bit_and (page_align - 1L) in
    let top_offset_poff = page_offset top_offset in
    let (p_offset, p_vaddr) = match (addr_spec) with
    (* Here the address and offset are given.*)
    | OffsetAddressSpec res -> res
    (* For this we need to generate an offset of the same alignment as the
       address provided here *)
    | AddressOnlySpec vaddr ->
        let vaddr_poff = page_offset vaddr in
        let add_to_offset =
          if vaddr_poff > top_offset_poff
          then vaddr_poff - top_offset_poff
          else (page_align + vaddr_poff) - top_offset_poff in
        (top_offset + add_to_offset, vaddr)
    (* For this we need to generate an virtual address of the same alignment
       as the offset provided here *)
    | OffsetOnlySpec offset ->
        (offset, top_vaddr + page_offset offset)
    (* Pick the top values for both *)
    | AnySpec -> (top_offset, top_vaddr + top_offset_poff) in

    (* Ensure that the offset and address values have the same page alignment *)
    let%bind _ = Result.of_option
      ~error:(fail "Offset and address not same page align") @@
      Option.guard (page_offset p_offset = page_offset p_vaddr) in
    let segm = {
      p_type; p_flags; p_offset; p_align; p_memsz;
      p_filesz; p_vaddr; p_paddr = p_vaddr;
    } in

    (* Check for any overlaps in the addresses or offsets in neighboring
       segments. *)
    let overlaps = List.fold_left ~init:false ~f:(||) [
      Option.exists ~f:(fun (_, prev) -> seg_olap_vaddr prev segm) @@ Map.closest_key
        image.i_segs.s_loads_by_vaddr `Less_or_equal_to segm.p_vaddr;
      Option.exists ~f:(fun (_, succ) -> seg_olap_vaddr segm succ) @@ Map.closest_key
        image.i_segs.s_loads_by_vaddr `Greater_or_equal_to segm.p_vaddr;
    ] in
    let%bind _ = Result.of_option
      ~error:(fail "Overlapping address or offset") @@
      Option.guard @@ not overlaps in

    (* Reallocate memory/PHDR as needed *)
    let image = ensure_mem_size image (p_offset + p_filesz) in

    (* Add in our new segment and update our image *)
    let%bind image = update_phdr_table image @@
      update_load_seg image.i_segs segm in
    let%bind mem = mem_of_segment image segm in
    let%map _ = Memory.write mem content in
    (image, segm, mem)
