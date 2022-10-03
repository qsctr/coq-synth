open Cmdliner
open Serlib
open Sexplib

let synth logical_dir physical_dir module_name hole_type max_depth params
extra_vars examples debug =
  Coq_synth.debug := debug;
  let sid = Coq_synth.load ~logical_dir ~physical_dir ~module_name in
  List.iter print_endline @@
    Coq_synth.synthesize ~sid ~hole_type ~max_depth ~params ~extra_vars
      ~examples

let () =
  let logical_dir =
    Arg.(required & opt (some string) None & info ["logical-dir"]) in
  let physical_dir =
    Arg.(required & opt (some dir) None & info ["physical-dir"]) in
  let module_name = Arg.(required & opt (some string) None & info ["module"]) in
  let hole_type = Arg.(required & opt (some string) None & info ["type"]) in
  let max_depth =
    let open Arg in
    let parser = parser_of_kind_of_string ~kind:"a nonnegative integer" @@
      fun str ->
        match int_of_string_opt str with
        | Some n when n >= 0 -> Some n
        | _ -> None in
    required & opt (some (conv (parser, Format.pp_print_int))) None
      & info ["max-depth"] in
  let params =
    let open Arg in
    value & opt (list (pair ~sep:':' string string)) [] & info ["params"] in
  let extra_vars = Arg.(value & opt (list string) [] & info ["extra-vars"]) in
  let examples =
    let open Arg in
    value & opt (list ~sep:';' (pair ~sep:'=' (list string) string)) []
      & info ["examples"] in
  let debug = Arg.(value & flag & info ["debug"]) in
  let open Term in
  exit @@ eval
    ( const synth $ logical_dir $ physical_dir $ module_name $ hole_type
        $ max_depth $ params $ extra_vars $ examples $ debug
    , info "coq_synth" )
