open Core_extend
open Bap_elf
open Std.Elf

type elf2 =
  { elf_: elf;
    e_phoff: int64;
    e_shoff: int64;
    e_flags: int32;
    e_ehsize: int64;
    e_phentsize: int64;
    e_shentsize: int64;
  }

let elf_32_sizes = (52L, 32L, 40L)
let elf_64_sizes = (64L, 56L, 64L)

let e_class_val = function
  | ELFCLASS32 -> 1
  | ELFCLASS64 -> 2

let e_data_val = function
  | ELFDATA2LSB -> 1
  | ELFDATA2MSB -> 2

let endian_of ei_data =
  match ei_data with
  | ELFDATA2LSB -> Bitstring.LittleEndian
  | ELFDATA2MSB -> Bitstring.BigEndian

let e_osabi_val = function
  | ELFOSABI_SYSV      -> 0
  | ELFOSABI_HPUX      -> 1
  | ELFOSABI_NETBSD    -> 2
  | ELFOSABI_LINUX     -> 3
  | ELFOSABI_SOLARIS   -> 6
  | ELFOSABI_AIX       -> 7
  | ELFOSABI_IRIX      -> 8
  | ELFOSABI_FREEBSD   -> 9
  | ELFOSABI_TRU64     -> 10
  | ELFOSABI_MODESTO   -> 11
  | ELFOSABI_OPENBSD   -> 12
  | ELFOSABI_ARM_AEABI -> 64
  | ELFOSABI_ARM       -> 97
  | ELFOSABI_EXT num   -> num
  | ELFOSABI_STANDALONE -> 255

let e_type_val = function
  | ET_NONE -> 0
  | ET_REL  -> 1
  | ET_EXEC -> 2
  | ET_DYN  -> 3
  | ET_CORE -> 4
  | ET_EXT num -> num

let e_machine_val = function
  | EM_NONE        -> 0
  | EM_M32         -> 1
  | EM_SPARC       -> 2
  | EM_386         -> 3
  | EM_68K         -> 4
  | EM_88K         -> 5
  | EM_860         -> 7
  | EM_MIPS        -> 8
  | EM_S370        -> 9
  | EM_MIPS_RS3_LE -> 10

  | EM_PARISC      -> 15
  | EM_VPP500      -> 17
  | EM_SPARC32PLUS -> 18
  | EM_960         -> 19
  | EM_PPC         -> 20
  | EM_PPC64       -> 21
  | EM_S390        -> 22

  | EM_V800        -> 36
  | EM_FR20        -> 37
  | EM_RH32        -> 38
  | EM_RCE         -> 39
  | EM_ARM         -> 40
  | EM_ALPHA       -> 41
  | EM_SH          -> 42
  | EM_SPARCV9     -> 43
  | EM_TRICORE     -> 44
  | EM_ARC         -> 45
  | EM_H8_300      -> 46
  | EM_H8_300H     -> 47
  | EM_H8S         -> 48
  | EM_H8_500      -> 49
  | EM_IA_64       -> 50
  | EM_MIPS_X      -> 51
  | EM_COLDFIRE    -> 52
  | EM_68HC12      -> 53
  | EM_MMA         -> 54
  | EM_PCP         -> 55
  | EM_NCPU        -> 56
  | EM_NDR1        -> 57
  | EM_STARCORE    -> 58
  | EM_ME16        -> 59
  | EM_ST100       -> 60
  | EM_TINYJ       -> 61
  | EM_X86_64      -> 62
  | EM_PDSP        -> 63

  | EM_FX66        -> 66
  | EM_ST9PLUS     -> 67
  | EM_ST7         -> 68
  | EM_68HC16      -> 69
  | EM_68HC11      -> 70
  | EM_68HC08      -> 71
  | EM_68HC05      -> 72
  | EM_SVX         -> 73
  | EM_ST19        -> 74
  | EM_VAX         -> 75
  | EM_CRIS        -> 76
  | EM_JAVELIN     -> 77
  | EM_FIREPATH    -> 78
  | EM_ZSP         -> 79
  | EM_MMIX        -> 80
  | EM_HUANY       -> 81
  | EM_PRISM       -> 82
  | EM_AVR         -> 83
  | EM_FR30        -> 84
  | EM_D10V        -> 85
  | EM_D30V        -> 86
  | EM_V850        -> 87
  | EM_M32R        -> 88
  | EM_MN10300     -> 89
  | EM_MN10200     -> 90
  | EM_PJ          -> 91
  | EM_OPENRISC    -> 92
  | EM_ARC_A5      -> 93
  | EM_XTENSA      -> 94
  | EM_AARCH64     -> 183
  | EM_TILEPRO     -> 188
  | EM_MICROBLAZE  -> 189
  | EM_TILEGX      -> 191
  | EM_EXT num -> num

let p_type_val = function
  | PT_NULL    -> 0l
  | PT_LOAD    -> 1l
  | PT_DYNAMIC -> 2l
  | PT_INTERP  -> 3l
  | PT_NOTE    -> 4l
  | PT_SHLIB   -> 5l
  | PT_PHDR    -> 6l
  | PT_OTHER num -> num

let p_flag_val = function
  | PF_X -> 0
  | PF_W -> 1
  | PF_R -> 2
  | PF_EXT num -> num

let sh_type_val = function
  | SHT_NULL     -> 0l
  | SHT_PROGBITS -> 1l
  | SHT_SYMTAB   -> 2l
  | SHT_STRTAB   -> 3l
  | SHT_RELA     -> 4l
  | SHT_HASH     -> 5l
  | SHT_DYNAMIC  -> 6l
  | SHT_NOTE     -> 7l
  | SHT_NOBITS   -> 8l
  | SHT_REL      -> 9l
  | SHT_SHLIB    -> 10l
  | SHT_DYNSYM   -> 11l
  | SHT_EXT num  -> num

let sh_flag_val = function
  | SHF_WRITE     -> 0
  | SHF_ALLOC     -> 1
  | SHF_EXECINSTR -> 2
  | SHF_EXT num   -> num

let flag_val to_flag flags = let open Int64 in
  List.fold_left ~f:bit_or ~init:0L @@
  List.map ~f:(Fn.compose (shift_left 1L) to_flag) flags

exception Pure_error of unit
let elf_err = fail "Invalid ELF input"
let purify fn =
  try Result.Ok (fn @@ Pure_error ())
  with Pure_error () -> Result.Error elf_err

let construct_elf_ident buf elf =
  let open Std.Elf in
  let open Result.Let_syntax in
  let char8 ch = purify @@ Bitstring.construct_char_unsigned buf ch 8 in
  let%bind _ = char8 0x7f in
  Bitstring.construct_string buf "ELF";
  let%bind _ = char8 @@ e_class_val elf.elf_.e_class in
  let%bind _ = char8 @@ e_data_val elf.elf_.e_data in
  let%bind _ = char8 elf.elf_.e_version in
  let%bind _ = char8 @@ e_osabi_val elf.elf_.e_osabi in
  let%map _ = char8 @@ elf.elf_.e_abiver in
  Bitstring.construct_string buf "\x00\x00\x00\x00\x00\x00\x00"

let construct_elf_hdr buf elf =
  let open Std.Elf in
  let open Result.Let_syntax in
  let open Result.Monad_infix in
  let endian = endian_of elf.elf_.e_data in
  let%bind _ = construct_elf_ident buf elf in
  let w_int16 num = purify @@
    Bitstring.construct_int_ee_unsigned endian buf num 16 in
  let w_int32_32 num = purify @@
    Bitstring.construct_int32_ee_unsigned endian buf num 32 in
  let w_int32_i num =
    let%bind num' = Result.of_option ~error:elf_err @@ Int32.of_int num in
    purify @@ Bitstring.construct_int32_ee_unsigned endian buf num' 32 in
  let w_int64_64 num ~fld = purify @@
    Bitstring.construct_int64_ee_unsigned endian buf num fld in
  match elf.elf_.e_class with
  | ELFCLASS32 ->
      let%bind _ = w_int16 @@ e_type_val elf.elf_.e_type in
      let%bind _ = w_int16 @@ e_machine_val elf.elf_.e_machine in
      let%bind _ = w_int32_i elf.elf_.e_version in
      let%bind _ = w_int64_64 ~fld:32 @@ elf.elf_.e_entry in
      let%bind _ = w_int64_64 ~fld:32 @@ elf.e_phoff in
      let%bind _ = w_int64_64 ~fld:32 @@ elf.e_shoff in
      let%bind _ = w_int32_32 elf.e_flags in
      let%bind _ = w_int64_64 ~fld:16 elf.e_ehsize in
      let%bind _ = w_int64_64 ~fld:16 elf.e_phentsize in
      let%bind _ = w_int16 @@ Sequence.length elf.elf_.e_segments in
      let%bind _ = w_int64_64 ~fld:16 elf.e_shentsize in
      let%bind _ = w_int16 @@ Sequence.length elf.elf_.e_sections in
                   w_int16 elf.elf_.e_shstrndx
  | ELFCLASS64 ->
      let%bind _ = w_int16 @@ e_type_val elf.elf_.e_type in
      let%bind _ = w_int16 @@ e_machine_val elf.elf_.e_machine in
      let%bind _ = w_int32_i elf.elf_.e_version in
      let%bind _ = w_int64_64 ~fld:64 @@ elf.elf_.e_entry in
      let%bind _ = w_int64_64 ~fld:64 @@ elf.e_phoff in
      let%bind _ = w_int64_64 ~fld:64 @@ elf.e_shoff in
      let%bind _ = w_int32_32 elf.e_flags in
      let%bind _ = w_int64_64 ~fld:16 elf.e_ehsize in
      let%bind _ = w_int64_64 ~fld:16 elf.e_phentsize in
      let%bind _ = w_int16 @@ Sequence.length elf.elf_.e_segments in
      let%bind _ = w_int64_64 ~fld:16 elf.e_shentsize in
      let%bind _ = w_int16 @@ Sequence.length elf.elf_.e_sections in
                   w_int16 elf.elf_.e_shstrndx

let construct_segment buf elf segm =
  let open Std.Elf in
  let open Result.Let_syntax in
  let open Result.Monad_infix in
  let endian = endian_of elf.elf_.e_data in
  let w_int32_32 num = purify @@
    Bitstring.construct_int32_ee_unsigned endian buf num 32 in
  let w_int64_64 num ~fld = purify @@
    Bitstring.construct_int64_ee_unsigned endian buf num fld in
  match elf.elf_.e_class with
  | ELFCLASS32 ->
      let%bind _ = w_int32_32 @@ p_type_val segm.p_type in
      let%bind _ = w_int64_64 ~fld:32 segm.p_offset in
      let%bind _ = w_int64_64 ~fld:32 segm.p_vaddr in
      let%bind _ = w_int64_64 ~fld:32 segm.p_paddr in
      let%bind _ = w_int64_64 ~fld:32 segm.p_filesz in
      let%bind _ = w_int64_64 ~fld:32 segm.p_memsz in
      let%bind _ = w_int64_64 ~fld:32 @@ flag_val p_flag_val segm.p_flags in
                   w_int64_64 ~fld:32 segm.p_align
  | ELFCLASS64 ->
      let%bind _ = w_int32_32 @@ p_type_val segm.p_type in
      let%bind _ = w_int64_64 ~fld:32 @@ flag_val p_flag_val segm.p_flags in
      let%bind _ = w_int64_64 ~fld:64 segm.p_offset in
      let%bind _ = w_int64_64 ~fld:64 segm.p_vaddr in
      let%bind _ = w_int64_64 ~fld:64 segm.p_paddr in
      let%bind _ = w_int64_64 ~fld:64 segm.p_filesz in
      let%bind _ = w_int64_64 ~fld:64 segm.p_memsz in
                   w_int64_64 ~fld:64 segm.p_align

let construct_section buf elf sect =
  let open Std.Elf in
  let open Result.Let_syntax in
  let open Result.Monad_infix in
  let endian = endian_of elf.elf_.e_data in
  let w_int32_32 num = purify @@
    Bitstring.construct_int32_ee_unsigned endian buf num 32 in
  let w_int32_i num =
    let%bind num' = Result.of_option ~error:elf_err @@ Int32.of_int num in
    purify @@ Bitstring.construct_int32_ee_unsigned endian buf num' 32 in
  let w_int64_64 num ~fld = purify @@
    Bitstring.construct_int64_ee_unsigned endian buf num fld in
  match elf.elf_.e_class with
  | ELFCLASS32 ->
      let%bind _ = w_int32_i @@ sect.sh_name in
      let%bind _ = w_int32_32 @@ sh_type_val sect.sh_type in
      let%bind _ = w_int64_64 ~fld:32 @@ flag_val sh_flag_val sect.sh_flags in
      let%bind _ = w_int64_64 ~fld:32 @@ sect.sh_addr in
      let%bind _ = w_int64_64 ~fld:32 @@ sect.sh_offset in
      let%bind _ = w_int64_64 ~fld:32 @@ sect.sh_size in
      let%bind _ = w_int32_32 @@ sect.sh_link in
      let%bind _ = w_int32_32 @@ sect.sh_info in
      let%bind _ = w_int64_64 ~fld:32 @@ sect.sh_addralign in
                   w_int64_64 ~fld:32 @@ sect.sh_entsize
  | ELFCLASS64 ->
      let%bind _ = w_int32_i @@ sect.sh_name in
      let%bind _ = w_int32_32 @@ sh_type_val sect.sh_type in
      let%bind _ = w_int64_64 ~fld:64 @@ flag_val sh_flag_val sect.sh_flags in
      let%bind _ = w_int64_64 ~fld:64 @@ sect.sh_addr in
      let%bind _ = w_int64_64 ~fld:64 @@ sect.sh_offset in
      let%bind _ = w_int64_64 ~fld:64 @@ sect.sh_size in
      let%bind _ = w_int32_32 @@ sect.sh_link in
      let%bind _ = w_int32_32 @@ sect.sh_info in
      let%bind _ = w_int64_64 ~fld:64 @@ sect.sh_addralign in
                   w_int64_64 ~fld:64 @@ sect.sh_entsize

let extend_elf_hdr elf raw_info =
  let open Result.Let_syntax in
  let endian = endian_of elf.e_data in
  let%map (e_phoff, e_shoff, e_flags) = match elf.e_class with
  | ELFCLASS32 -> (match%bitstring raw_info with
      | {|0x7F:8; "ELF": 24: string;
          _magic     : 12*8: bitstring;
          _e_type    : 16 : endian (endian);
          _e_machine : 16 : endian (endian);
          _e_version : 32 : endian (endian);
          _e_entry   : 32 : endian (endian);
          e_phoff    : 32 : endian (endian);
          e_shoff    : 32 : endian (endian);
          e_flags    : 32 : endian (endian);
          _rest      : -1 : bitstring
        |} -> Result.Ok
          (Int64.of_int32 e_phoff, Int64.of_int32 e_shoff, e_flags)
      | {| _ |} -> Result.Error (fail "Invalid ELF header"))
  | ELFCLASS64 -> (match%bitstring raw_info with
      | {|0x7F:8; "ELF": 24: string;
          _magic     : 12*8: bitstring;
          _e_type    : 16 : endian (endian);
          _e_machine : 16 : endian (endian);
          _e_version : 32 : endian (endian);
          _e_entry   : 64 : endian (endian);
          e_phoff    : 64 : endian (endian);
          e_shoff    : 64 : endian (endian);
          e_flags    : 32 : endian (endian);
          _rest      : -1 : bitstring
        |} -> Result.Ok (e_phoff, e_shoff, e_flags)
      | {| _ |} -> Result.Error (fail "Invalid ELF header")) in
  let (e_ehsize, e_phentsize, e_shentsize) =
    match elf.e_class with
    | ELFCLASS32 -> elf_32_sizes
    | ELFCLASS64 -> elf_64_sizes in
  { elf_ = elf;
    e_phoff; e_shoff; e_flags;
    e_ehsize; e_phentsize; e_shentsize;
  }

let write_elf_ehdr elf bs =
  let buf = Bitstring.Buffer.create () in
  let open Result.Let_syntax in
  let%map () = construct_elf_hdr buf elf in
  let (data, _, _) = Bitstring.Buffer.contents buf in
  Bigstring.From_bytes.blito ~src:data ~dst:bs ()

let write_elf_phdr elf bs =
  let buf = Bitstring.Buffer.create () in
  let open Result.Let_syntax in
  let%bind () = Sequence.fold_m ~bind:Result.bind ~return:Result.return ~init:()
    ~f:(const @@ construct_segment buf elf) elf.elf_.e_segments in
  let%map off = Int64.to_int_err elf.e_phoff in
  let (data, _, _) = Bitstring.Buffer.contents buf in
  Bigstring.From_bytes.blito ~src:data ~dst:bs ~dst_pos:off ()

let write_elf_shdr elf bs =
  let buf = Bitstring.Buffer.create () in
  let open Result.Let_syntax in
  let%bind () = Sequence.fold_m ~bind:Result.bind ~return:Result.return ~init:()
    ~f:(const @@ construct_section buf elf) elf.elf_.e_sections in
  let%map off = Int64.to_int_err elf.e_shoff in
  let (data, _, _) = Bitstring.Buffer.contents buf in
  Bigstring.From_bytes.blito ~src:data ~dst:bs ~dst_pos:off ()
