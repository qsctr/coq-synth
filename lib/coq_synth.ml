open Serapi
open Serlib
open Sertop

let rec last =
  function
  | [] -> failwith "last []"
  | [x] -> x
  | _::xs -> last xs

module ConstrHashtbl = struct
  include Hashtbl.Make(Constr)

  let find_or_add ht def k =
    match find_opt ht k with
    | Some v -> v
    | None ->
      let v = def () in
      add ht k v;
      v

  let add_multi ht k v =
    match find_opt ht k with
    | Some vs -> replace ht k (v :: vs)
    | None -> add ht k [v]

  let find_multi ht k =
    match find_opt ht k with
    | Some vs -> vs
    | None -> []
end

module IndHash = struct
  type t = Names.inductive
  let equal = Names.eq_ind
  let hash = Names.ind_hash
end
module IndHashtbl = Hashtbl.Make(IndHash)

let exec_get cmd =
  match Serapi_protocol.exec_cmd cmd with
  | ObjList [obj] :: _ -> obj
  | x -> failwith @@
    Sexplib.Sexp.to_string_hum (Sertop_ser.sexp_of_cmd cmd) ^ "\n -> \n" ^
      Sexplib.Sexp.to_string_hum
        (Sexplib.Conv.sexp_of_list Sertop_ser.sexp_of_answer_kind x)

let [@warning "-8"] synthesize sid n extra_names =
  if n < 0 then
    invalid_arg "n must be nonnegative";
  let query_opt : Serapi_protocol.query_opt =
    { preds = []
    ; limit = None
    ; sid
    ; pp =
      { pp_format = PpSer
      ; pp_depth = 5
      ; pp_elide = "..."
      ; pp_margin = 72
      }
    ; route = Feedback.default_route
    } in
  let query q = exec_get (Query (query_opt, q)) in
  match query Env, query Goals with
  | CoqEnv env, CoqGoal {goals = [{ty = goal_type; _}]; _} ->
    let atoms = ConstrHashtbl.create 16 in
    let returning = ConstrHashtbl.create 16 in
    let find_returning =
      ConstrHashtbl.find_or_add returning
        (fun () -> ConstrHashtbl.create 16) in
    let rec add_returning t =
      match Constr.kind t with
      | Prod (_, _, r) ->
        ConstrHashtbl.replace (find_returning r) t ();
        add_returning r
      | _ -> ()
    in
    let add_var atom t =
      add_returning t;
      ConstrHashtbl.add_multi atoms t atom
    in
    extra_names |> List.iter
      begin fun name ->
        match query (TypeOf name) with
        | CoqConstr t ->
          let glob_ref = Nametab.locate (Libnames.qualid_of_string name) in
          add_var (Constr.mkRef (glob_ref, Univ.Instance.empty)) t
      end;
    let ctors_added = IndHashtbl.create 16 in
    let add_ctors ind =
      if not (IndHashtbl.mem ctors_added ind) then
        let ind_str = Pp.string_of_ppcmds (Printer.pr_inductive env ind) in
        match query (Definition ind_str) with
        | CoqMInd (_, {mind_packets; _}) ->
          let n_ctors = Array.length mind_packets.(snd ind).mind_consnames in
          for ctor_ix = 1 to n_ctors do
            let ctor = Names.ith_constructor_of_inductive ind ctor_ix in
            let t, _ =
              Typeops.type_of_global_in_context env
                (Names.GlobRef.ConstructRef ctor) in
            add_var (Constr.mkConstruct ctor) t
          done;
          IndHashtbl.add ctors_added ind ()
    in
    let terms = ConstrHashtbl.create 16 in
    let mk_terms_arr () = Array.make n None in
    let rec synth ty m =
      begin match Constr.kind ty with
        | Ind (ind, _) -> add_ctors ind
        | _ -> ()
      end;
      let tms = ConstrHashtbl.find_or_add terms mk_terms_arr ty in
      match tms.(m) with
      | Some ts -> ts
      | None ->
        let ts =
          if m = 0 then
            ConstrHashtbl.find_multi atoms ty
          else
            let prods = ConstrHashtbl.to_seq_keys (find_returning ty) in
            let depths =
              List.to_seq
                (List.concat (List.init (m - 1) (fun i -> [i, m - 1; m - 1, i]))
                  @ [m - 1, m - 1]) in
            depths
              |> Seq.flat_map
                begin fun (arg_depth, prod_depth) ->
                  prods |> Seq.flat_map
                    begin fun prod ->
                      let _, arg_ty, _ = Constr.destProd prod in
                      let arg_ts = List.to_seq (synth arg_ty arg_depth) in
                      let prod_ts = List.to_seq (synth prod prod_depth) in
                      arg_ts |> Seq.flat_map
                        begin fun arg_tm ->
                          prod_ts |> Seq.map
                            begin fun prod_tm ->
                              Constr.mkApp (prod_tm, [|arg_tm|])
                            end
                        end
                    end
                end
              |> List.of_seq
        in
        tms.(m) <- Some ts;
        ts
    in
    List.concat (List.init n (synth goal_type))

let load file =
  Serlib_init.init
    ~options:
      { omit_loc = false
      ; omit_att = false
      ; exn_on_opaque = false
      };
  Sertop_init.coq_init
    { fb_handler = ignore
    ; ml_load = None
    ; debug = false
    };
  ignore @@ Serapi_protocol.exec_cmd @@ NewDoc
    { top_name = TopLogical
      (Names.DirPath.make [Names.Id.of_string "Coq_synth"])
    ; iload_path = None
    ; require_libs = None
    };
  let sids =
    Serapi_protocol.exec_cmd (ReadFile file)
      |> List.to_seq
      |> Seq.filter_map
        begin function
          | Serapi_protocol.Added (sid, _, _) -> Some sid
          | Serapi_protocol.CoqExn _ as ak ->
            failwith
              (Sexplib.Sexp.to_string_hum (Sertop_ser.sexp_of_answer_kind ak))
          | _ -> None
        end
      |> List.of_seq
  in
  sids |> List.iter (fun sid -> ignore (Serapi_protocol.exec_cmd (Exec sid)));
  last sids

let [@warning "-8"] print fmt sid term =
  let pp : Serapi_protocol.format_opt =
    { pp_format = PpCoq
    ; pp_depth = 5
    ; pp_elide = "..."
    ; pp_margin = 72
    } in
  match exec_get (Print ({sid; pp}, CoqConstr term)) with
  | CoqPp pp -> Pp.pp_with fmt pp
