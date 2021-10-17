
open Bap.Std
open Bap_main
open Core_kernel

type Extension.Error.t += SegmentFailure of Error.t

let fail e = SegmentFailure e

let debug = Extension.Command.flag
  ~aliases:["v"]
  ~doc:"Whether to enable verbose debugging or not"
  "verbose"
let input = Extension.Command.parameter
  ~aliases:["i"]
  ~doc:"The input file"
  Extension.Type.("FILE" %: file ) "input"
let output = Extension.Command.parameter
  ~aliases:["o"]
  ~doc:"The output file"
  Extension.Type.("FILE" %: string ) "output"

let main input output =
  let open Result.Let_syntax in
  let open Elf_segments in
  let%bind image = load_image input in
  let%map image = Rewriter.rewrite image in
  save_image image output

let () = Extension.Command.(begin
    declare "segments" (args $debug $input $output)
      ~requires:["loader"]
  end) @@ fun debug input output _ctxt ->
    let open Result.Let_syntax in
    let () = Rewriter.is_debug := debug in
    let res = main input output in
    Result.map_error ~f:fail res

let () = Extension.Error.register_printer @@ function
  | SegmentFailure err -> Some ("segments: " ^ Error.to_string_hum err)
  | _ -> None
