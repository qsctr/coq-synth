open Cmdliner

let synth logical_dir physical_dir module_name hole_type max_depth params
extra_vars examples debug =
  Coq_synth.debug := debug;
  let sid = Coq_synth.load ~logical_dir ~physical_dir ~module_name in
  List.iter print_endline @@
    Coq_synth.synthesize ~sid ~hole_type ~max_depth ~params ~extra_vars
      ~examples

let () =
  let logical_dir =
    let open Arg in
    required & opt (some string) None
      & info ~doc:"The logical directory of the Coq module" ~docv:"DIRPATH"
        ["logical-dir"] in
  let physical_dir =
    let open Arg in
    required & opt (some dir) None
      & info ~doc:"The physical directory of the Coq module" ~docv:"DIR"
        ["physical-dir"] in
  let module_name =
    let open Arg in
    required & opt (some string) None
      & info ~doc:"The name of the Coq module" ~docv:"MOD" ["module"] in
  let hole_type =
    let open Arg in
    required & opt (some string) None
      & info ~doc:"The type of the terms to synthesize" ~docv:"TYPE" ["type"] in
  let max_depth =
    let open Arg in
    let parser = parser_of_kind_of_string ~kind:"a nonnegative integer" @@
      fun str ->
        match int_of_string_opt str with
        | Some n when n >= 0 -> Some n
        | _ -> None in
    required & opt (some (conv (parser, Format.pp_print_int))) None
      & info ~doc:"The maximum depth of terms to synthesize" ~docv:"N"
        ["max-depth"] in
  let params =
    let open Arg in
    value & opt (list (pair ~sep:':' string string)) []
      & info ~doc:"The parameters to the synthesized terms"
        ~docv:"PARAM1:TYPE1,PARAM2:TYPE2,..." ["params"] in
  let extra_vars =
    let open Arg in
    value & opt (list string) []
      & info
        ~doc:"Extra variables (already defined) to include in the \
          synthesized terms"
        ~docv:"VAR1,VAR2,..." ["extra-vars"] in
  let examples =
    let open Arg in
    value & opt (list ~sep:';' (pair ~sep:'=' (list string) string)) []
      & info
        ~doc:"Input-output examples that the synthesized terms must satisfy"
        ~docv:"INPUT1A,INPUT1B,...=OUTPUT1;INPUT2A,INPUT2B,...=OUTPUT2;..."
        ["examples"] in
  let debug =
    Arg.(value & flag & info ~doc:"Enable debug output to stderr" ["debug"]) in
  let open Term in
  exit @@ eval
    ( const synth $ logical_dir $ physical_dir $ module_name $ hole_type
        $ max_depth $ params $ extra_vars $ examples $ debug
    , info ~doc:"Coq synthesizer" "coq_synth" )
