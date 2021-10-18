
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

let main mmapfile minput moutput =
  let open Result.Let_syntax in
  let open Elf_segments in
  let%bind input = Result.of_option
    ~error:(Error.of_string "Need an input file") minput in
  let%bind output = Result.of_option
    ~error:(Error.of_string "Need an output file") moutput in
  let%bind image = load_image input in
  let%map image = Rewriter.rewrite image mmapfile in
  save_image image output

let () = Extension.Command.(begin
    declare "segments" (args $debug $mapfile $input $output)
      ~requires:["loader"]
  end) @@ fun debug mapfile input output _ctxt ->
    let open Result.Let_syntax in
    let () = Rewriter.is_debug := debug in
    let res = main mapfile input output in
    Result.map_error ~f:(fun e -> SegmentFailure e) res

let () = Extension.Error.register_printer @@ function
  | SegmentFailure err -> Some ("segments: " ^ Error.to_string_hum err)
  | _ -> None
