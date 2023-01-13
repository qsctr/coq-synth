open Cmdliner

let synth logical_dir physical_dir module_name hole_type params extra_exprs
examples k levels debug =
  Coq_synth.debug := debug;
  Coq_synth.with_error_handler (fun e -> `Error (false, e)) @@ fun () ->
    let sid = Coq_synth.load ~logical_dir ~physical_dir ~module_name in
    Base.Sequence.iter
      (Coq_synth.synthesize ~sid ~hole_type ~params ~extra_exprs ~examples
        ~k ~levels)
      ~f:print_endline;
    `Ok ()

let nonneg =
  let open Arg in
  let parser = parser_of_kind_of_string ~kind:"a nonnegative integer" @@
    fun str ->
      match int_of_string_opt str with
      | Some n when n >= 0 -> Some n
      | _ -> None in
  conv (parser, Format.pp_print_int)

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
  let params =
    let open Arg in
    value & opt (list (pair ~sep:':' string string)) []
      & info ~doc:"The parameters to the synthesized terms"
        ~docv:"PARAM1:TYPE1,PARAM2:TYPE2,..." ["params"] in
  let extra_exprs =
    let open Arg in
    value & opt (list string) []
      & info
        ~doc:"Extra expressions (containing already defined variables) to \
          include in the synthesized terms"
        ~docv:"EXPR1,EXPR2,..." ["extra-exprs"] in
  let examples =
    let open Arg in
    value & opt (list ~sep:';' (pair ~sep:'=' (list string) string)) []
      & info
        ~doc:"Input-output examples that the synthesized terms must satisfy"
        ~docv:"INPUT1A,INPUT1B,...=OUTPUT1;INPUT2A,INPUT2B,...=OUTPUT2;..."
        ["examples"] in
  let k =
    let open Arg in
    value & opt (some ~none:"infinity" nonneg) None
      & info ~doc:"The maximum number of terms to return" ~docv:"K"
        ["num-terms"] in
  let levels =
    let open Arg in
    value & opt (some ~none:"infinity" nonneg) None
      & info
          ~doc:"The maximum search depth (note: this does not necessarily \
            correspond to the depth of terms due to simplification)"
          ~docv:"N" ["max-depth"] in
  let debug =
    Arg.(value & flag & info ~doc:"Enable debug output to stderr" ["debug"]) in
  let open Term in
  let exits = exit_info ~doc:"on Coq error." 1 :: default_exits in
  exit @@ eval begin
    ret begin
      const synth $ logical_dir $ physical_dir $ module_name $ hole_type
        $ params $ extra_exprs $ examples $ k $ levels $ debug
    end,
    info ~doc:"Coq synthesizer" ~exits "coq_synth"
  end
