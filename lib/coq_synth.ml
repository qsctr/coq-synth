open Base
open Serapi
open Serlib
open Sertop

module ConstrHash = struct
  include Constr
  let sexp_of_t = Ser_constr.sexp_of_t
end

module IndHash = struct
  type t = Names.inductive
  let compare = Names.ind_ord
  let hash = Names.ind_hash
  let sexp_of_t = Ser_names.sexp_of_inductive
end

let exec_get cmd =
  match Serapi_protocol.exec_cmd cmd with
  | ObjList [obj] :: _ -> obj
  | x -> failwith @@
    Sexp.to_string_hum (Sertop_ser.sexp_of_cmd cmd) ^ "\n -> \n" ^
      Sexp.to_string_hum (List.sexp_of_t Sertop_ser.sexp_of_answer_kind x)

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
    let atoms = Hashtbl.create (module ConstrHash) in
    let returning = Hashtbl.create (module ConstrHash) in
    let find_returning =
      Hashtbl.find_or_add returning
        ~default:(fun () -> Hash_set.create (module ConstrHash)) in
    let rec add_returning t =
      match Constr.kind t with
      | Prod (_, _, r) ->
        Hash_set.add (find_returning r) t;
        add_returning r
      | _ -> ()
    in
    let add_var atom t =
      add_returning t;
      Hashtbl.add_multi atoms ~key:t ~data:atom
    in
    List.iter extra_names ~f:begin fun name ->
      match query (TypeOf name) with
      | CoqConstr t ->
        let glob_ref = Nametab.locate (Libnames.qualid_of_string name) in
        add_var (Constr.mkRef (glob_ref, Univ.Instance.empty)) t
    end;
    let ctors_added = Hash_set.create (module IndHash) in
    let add_ctors ind =
      if not (Hash_set.mem ctors_added ind) then
        let ind_str = Pp.string_of_ppcmds (Printer.pr_inductive env ind) in
        match query (Definition ind_str) with
        | CoqMInd (_, {mind_packets; _}) ->
          let n_ctors = Array.length mind_packets.(snd ind).mind_consnames in
          for ctor_ix = 1 to n_ctors do
            let ctor = Names.ith_constructor_of_inductive ind ctor_ix in
            let ctor_str =
              Pp.string_of_ppcmds
                (Printer.pr_global_env
                  (Termops.vars_of_env env)
                  (Names.GlobRef.ConstructRef ctor)) in
            match query (TypeOf ctor_str) with
            | CoqConstr t -> add_var (Constr.mkConstruct ctor) t
          done;
          Hash_set.add ctors_added ind
    in
    let terms = Hashtbl.create (module ConstrHash) in
    let mk_terms_arr () = Option_array.create ~len:n in
    let rec synth ty m =
      begin match Constr.kind ty with
        | Ind (ind, _) -> add_ctors ind
        | _ -> ()
      end;
      let tms = Hashtbl.find_or_add terms ty ~default:mk_terms_arr in
      match Option_array.get tms m with
      | Some ts -> ts
      | None ->
        let ts =
          if m = 0 then
            Hashtbl.find_multi atoms ty
          else
            let open List.Monad_infix in
            let prods = Hash_set.to_list (find_returning ty) in
            let depths =
              (List.range 0 (m - 1) >>= (fun i -> [i, m - 1; m - 1, i]))
                @ [m - 1, m - 1] in
            depths >>= fun (arg_depth, prod_depth) ->
              prods >>= fun prod ->
                let _, arg_ty, _ = Constr.destProd prod in
                let arg_ts = synth arg_ty arg_depth in
                let prod_ts = synth prod prod_depth in
                arg_ts >>= fun arg_tm ->
                  prod_ts >>| fun prod_tm ->
                    Constr.mkApp (prod_tm, [|arg_tm|])
        in
        Option_array.set_some tms m ts;
        ts
    in
    List.concat (List.init n ~f:(synth goal_type))

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
    List.filter_map
      (Serapi_protocol.exec_cmd (ReadFile file))
      ~f:begin function
        | Serapi_protocol.Added (sid, _, _) -> Some sid
        | Serapi_protocol.CoqExn _ as ak ->
          failwith (Sexp.to_string_hum (Sertop_ser.sexp_of_answer_kind ak))
        | _ -> None
      end
  in
  List.iter sids ~f:(fun sid -> ignore (Serapi_protocol.exec_cmd (Exec sid)));
  List.last_exn sids

let [@warning "-8"] print fmt sid term =
  let pp : Serapi_protocol.format_opt =
    { pp_format = PpCoq
    ; pp_depth = 5
    ; pp_elide = "..."
    ; pp_margin = 72
    } in
  match exec_get (Print ({sid; pp}, CoqConstr term)) with
  | CoqPp pp -> Pp.pp_with fmt pp
