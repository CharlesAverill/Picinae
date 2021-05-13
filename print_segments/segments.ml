
open Bap.Std
open Bap_main

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
  match Image.create ~backend:"llvm" input with
  | Error err ->
    Core_kernel.invalid_argf "failed to parse the file: %s"
      (Core_kernel.Error.to_string_hum err) ()
  | Ok (img,_warns) ->
    Rewriter.rewrite img table_output text_output; Ok ()

