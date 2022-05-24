let [@warning "-8"] _ =
  match Array.to_list Sys.argv with
  | _ :: file :: n :: extra_names ->
    let sid = Coq_synth.load file in
    Coq_synth.synthesize sid (int_of_string n) extra_names
      |> List.iter
        begin function term ->
          Coq_synth.print Format.std_formatter sid term;
          Format.print_newline ()
        end
