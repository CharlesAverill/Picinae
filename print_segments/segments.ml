
open Bap.Std
open Bap_main
open Core_kernel

type Extension.Error.t += SegmentFailure of Error.t

let fail e = SegmentFailure e

(* Combined, this functions as the entrypoint of the plugin, to be called as:
$ bap segments /path/to/riscv32/binary
*)
let input = Extension.Command.argument
  ~doc:"The input file" Extension.Type.("FILE" %: string =? "a.out" )
let output = Extension.Command.argument
  ~doc:"The output file" Extension.Type.("FILE" %: string =? "a.out.patched" )

let main input output =
  let open Result.Let_syntax in
  let open Elf_segments in
  let%bind image = load_image input in
  let%bind (image, segm) = new_segment
    ?filesz:(Some 0x1000)
    ?p_flags:(Some [])
    image AnySpec in
  let%map (image, segm) = new_segment
    ?filesz:(Some 0x1000)
    image AnySpec in
  save_image image output

let () = Extension.Command.(begin
    declare "segments" (args $input $output)
      ~requires:["loader"]
  end) @@ fun input output _ctxt ->
    let res = let open Result.Let_syntax in
      (*
      let%bind (img,_warns) = Image.create ~backend:"llvm" input in
      let%map _ = Rewriter.rewrite img table_output text_output in ()
      *)
      main input output
     in Result.map_error ~f:fail res

let () = Extension.Error.register_printer @@ function
  | SegmentFailure err -> Some ("segments: " ^ Error.to_string_hum err)
  | _ -> None
