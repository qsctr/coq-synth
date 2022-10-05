open Base
open Serapi
open Serlib
open Sertop

let debug = ref false

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

let exec cmd =
  let pp_err sexp =
    let open Caml.Format in
    Sexp.pp_hum err_formatter sexp;
    pp_print_newline err_formatter () in
  if !debug then
    pp_err (Sertop_ser.sexp_of_cmd cmd);
  let aks = Serapi_protocol.exec_cmd cmd in
  if !debug then
    pp_err (sexp_of_list Sertop_ser.sexp_of_answer_kind aks);
  aks

let exec_get cmd =
  match exec cmd with
  | ObjList [obj] :: _ -> obj
  | res ->
    let open Error in
    raise @@ of_list
      [ create "Command" cmd Sertop_ser.sexp_of_cmd
      ; create "returned" res
          (sexp_of_list Sertop_ser.sexp_of_answer_kind) ]

let parse expr_str =
  let vernac_str = Printf.sprintf "Check %s." expr_str in
  match exec_get (Parse ({ontop = None}, vernac_str)) with
  | CoqAst {v = {expr = VernacCheckMayEval (_, _, constrexpr); _}; _} ->
    constrexpr
  | _ -> assert false

(* let print_sexp sexp =
  Sexp.pp_hum Caml.Format.std_formatter sexp;
  Caml.Format.print_newline () *)

let load ~logical_dir ~physical_dir ~module_name =
  Serlib_init.init
    ~options:
      { omit_loc = false
      ; omit_att = false
      ; exn_on_opaque = false };
  Sertop_init.coq_init
    { fb_handler = ignore
    ; ml_load = None
    ; debug = false };
  let ldir = Libnames.dirpath_of_string @@
    if String.(logical_dir = "<>") then "" else logical_dir in
  ignore @@ exec @@ NewDoc
    { top_name = TopLogical (Libnames.dirpath_of_string "Coq_synth")
    ; iload_path = Some
        (Serapi_paths.coq_loadpath_default ~implicit:true
          ~coq_path:Coq_config.coqlib
        @ [ { path_spec = VoPath
                { unix_path = physical_dir
                ; coq_path = ldir
                ; implicit = true
                ; has_ml = AddNoML }
            ; recursive = true } ])
    ; require_libs = None };
  let sentences = Printf.sprintf
    "Load LFindLoad. From %s Require Import %s."
    (Names.DirPath.to_string ldir) module_name in
  let sids =
    exec (Add
      ({lim = None; ontop = None; newtip = None; verb = false}, sentences))
    |> List.filter_map ~f:begin function
      | Serapi_protocol.Added (sid, _, _) -> Some sid
      | _ -> None
    end in
  List.iter sids ~f:(fun sid -> ignore (exec (Exec sid)));
  List.last_exn sids

let synthesize ~sid ~hole_type ~max_depth ~params ~extra_vars ~examples =
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
    ; route = Feedback.default_route } in
  match exec_get (Query (query_opt, Env)) with
  | CoqEnv env ->
    let globref_of_string s = Nametab.locate (Libnames.qualid_of_string s) in
    let constr_of_globref g = Constr.mkRef (g, Univ.Instance.empty) in
    let type_of_globref g = fst (Typeops.type_of_global_in_context env g) in
    let hole_ty = constr_of_globref (globref_of_string hole_type) in
    let pars = List.map params ~f:begin fun (param_name, param_type) ->
      Names.Id.of_string param_name,
      constr_of_globref (globref_of_string param_type)
    end in
    let constr_of_string s = EConstr.to_constr Evd.empty
      (fst (Constrintern.interp_constr env Evd.empty (parse s))) in
    let exs = List.map examples ~f:begin fun (inputs, output) ->
      List.map2_exn pars inputs
        ~f:(fun (name, _) inp -> name, constr_of_string inp),
      constr_of_string output
    end in
    let atoms = Hashtbl.create (module ConstrHash) in
    let returning = Hashtbl.create (module ConstrHash) in
    let find_returning = Hashtbl.find_or_add returning
      ~default:(fun () -> Hash_set.create (module ConstrHash)) in
    let rec add_returning t =
      match Constr.kind t with
      | Prod (_, _, r) ->
        Hash_set.add (find_returning r) t;
        add_returning r
      | _ -> () in
    let add_var atom t =
      add_returning t;
      Hashtbl.add_multi atoms ~key:t ~data:atom in
    List.iter pars ~f:begin fun (par_name, par_type) ->
      add_var (Constr.mkVar par_name) par_type
    end;
    List.iter extra_vars ~f:begin fun var ->
      let globref = globref_of_string var in
      add_var (constr_of_globref globref) (type_of_globref globref)
    end;
    let ctors_added = Hash_set.create (module IndHash) in
    let add_ctors ind =
      if not (Hash_set.mem ctors_added ind) then
        let packets = (Environ.lookup_mind (fst ind) env).mind_packets in
        for ctor_ix = 1 to Array.length packets.(snd ind).mind_consnames do
          let ctor = Names.ith_constructor_of_inductive ind ctor_ix in
          add_var (Constr.mkConstruct ctor)
            (type_of_globref (ConstructRef ctor))
        done;
        Hash_set.add ctors_added ind in
    let terms = Hashtbl.create (module ConstrHash) in
    let rec synth ty n =
      begin match Constr.kind ty with
      | Ind (ind, _) -> add_ctors ind
      | _ -> ()
      end;
      let tms = Hashtbl.find_or_add terms ty
        ~default:(fun () -> Option_array.create ~len:max_depth) in
      match Option_array.get tms n with
      | Some ts -> ts
      | None ->
        let ts =
          if n = 0 then
            Hashtbl.find_multi atoms ty
          else
            let open List.Monad_infix in
            let prods = Hash_set.to_list (find_returning ty) in
            let depths =
              (List.range 0 (n - 1) >>= fun i -> [i, n - 1; n - 1, i])
              @ [n - 1, n - 1] in
            depths >>= fun (arg_depth, prod_depth) ->
              prods >>= fun prod ->
                let _, arg_ty, _ = Constr.destProd prod in
                let arg_ts = synth arg_ty arg_depth in
                let prod_ts = synth prod prod_depth in
                arg_ts >>= fun arg_tm ->
                  prod_ts >>| fun prod_tm ->
                    Constr.mkApp (prod_tm, [|arg_tm|]) in
        Option_array.set_some tms n ts;
        ts in
    List.init max_depth ~f:(synth hole_ty)
      |> List.concat
      |> List.filter ~f:begin fun term ->
        try
          List.iter exs ~f:begin fun (subst, output) ->
            Reduction.conv env (Vars.replace_vars subst term) output
          end;
          true
        with Reduction.NotConvertible ->
          false
      end
      |> List.map ~f:begin fun term ->
        Pp.string_of_ppcmds (Printer.pr_constr_env env Evd.empty term)
      end
  | _ -> assert false
