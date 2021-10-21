
open Bap.Std
open Bap_main
open Core_extend

type Extension.Error.t += SegmentFailure of Error.t

let debug = Extension.Command.flag
  ~aliases:["v"]
  ~doc:"Whether to enable verbose debugging or not"
  "verbose"
let mapfile = Extension.Command.parameter
  ~aliases:["m"]
  ~doc:("Determines wether to write out a map file describing the address " ^
  " mappings of old code locations to new code locations.")
  Extension.Type.("FILE" %: some string ) "mapfile"
let input = Extension.Command.parameter
  ~aliases:["i"]
  ~doc:"The input file"
  Extension.Type.("FILE" %: some file ) "input"
let output = Extension.Command.parameter
  ~aliases:["o"]
  ~doc:"The output file"
  Extension.Type.("FILE" %: some string ) "output"

type abort_handler_spec = {
  spec_name: string;
  spec_doc: string;
  spec_handler: int list;
}

let spec_name s = s.spec_name
let spec_doc s = s.spec_doc
let spec_handler s = s.spec_handler

let abort_handlers =
  [
    {
      spec_name = "handler-none";
      spec_doc  = "(default) Insert no abort handler for CFI faults";
      spec_handler = [];
    };
    {
      spec_name = "handler-linux-abort";
      spec_doc  = "Inserts a linux syscall to kill(getpid(), ABORT)";
      spec_handler = [
        (* see abort.s for disassembly *)
        (* write error message *)
        0x00100513; 0x00000597; 0x03858593; 0x01800613; 0x04000893; 0x00000073;
        (* get current PID *)
        0x0ac00893; 0x00000073;
        (* kill SIGABRT *)
        0x00600593; 0x08100893; 0x00000073;
        (* exit -1 *)
        0xfff00513; 0x05d00893; 0x00000073;
        (* infinite loop *)
        0x0000006f;
        (* the actual error message *)
        0x46432a2a; 0x6f702049; 0x7963696c; 0x6f697620; 0x6974616c; 0x0a216e6f;
      ];
    };
  ]
let aborts = Extension.Command.switch
  ~doc:spec_doc
  abort_handlers spec_name


let () = Extension.Command.(begin
    declare "riscv-cfi" (args $debug $aborts $mapfile $input $output)
      ~doc:"Rewrites Riscv32 binaries to have CFI"
      ~requires:["loader"]

  end) @@ fun debug aborts map_file input output _ctxt ->
    let () = is_debug := debug in
    let res =
      let open Result.Let_syntax in
      let open Elf_segments in
      let abort_handler = Option.inject aborts ~def:[] ~f:spec_handler in
      let%bind input = Result.of_option
        ~error:(Error.of_string "Need an input file") input in
      let%bind output = Result.of_option
        ~error:(Error.of_string "Need an output file") output in
      let%bind image = load_image input in
      let%map image = Rewriter.rewrite image map_file abort_handler in
      save_image image output in
    Result.map_error ~f:(fun e -> SegmentFailure e) res

let () = Extension.Error.register_printer @@ function
  | SegmentFailure err -> Some ("riscv-cfi: " ^ Error.to_string_hum err)
  | _ -> None
