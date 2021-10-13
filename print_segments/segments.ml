
open Bap.Std
open Bap_main
open Core_kernel

type Extension.Error.t += SegmentFailure of Error.t

let fail e = SegmentFailure e

(* Combined, this functions as the entrypoint of the plugin, to be called as:
$ bap segments /path/to/riscv32/binary
*)
let input = Extension.Command.argument
  ~doc:"The input file" Extension.Type.("FILE" %: string =? "a.in" )
let table_output = Extension.Command.argument
  ~doc:"The table output file" Extension.Type.("FILE" %: string =? "table.bin" )
let text_output = Extension.Command.argument
  ~doc:"The text output file" Extension.Type.("FILE" %: string =? "text.bin" )
let () = Extension.Command.(begin
    declare "segments" (args $input $table_output $text_output)
      ~requires:["loader"]
  end) @@ fun input table_output text_output _ctxt ->
    let res = let open Result.Let_syntax in
      let%bind (img,_warns) = Image.create ~backend:"llvm" input in
      let%map _ = Rewriter.rewrite img table_output text_output in ()
     in Result.map_error ~f:fail res

let () = Extension.Error.register_printer @@ function
  | SegmentFailure err -> Some ("segments: " ^ Error.to_string_hum err)
  | _ -> None
