open Base
open Serapi
open Serlib
open Sertop

let debug = ref false

module ConstrHash = struct
  include Constr
  let sexp_of_t = Ser_constr.sexp_of_t
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

let reduce_econstr env sigma =
  let reduction, _ = Redexpr.reduction_of_red_expr env @@ Cbn
    { rBeta = true
    ; rMatch = true
    ; rFix = true
    ; rCofix = true
    ; rZeta = true
    ; rDelta = true
    ; rConst = [] } in
  fun term -> EConstr.Unsafe.to_constr (snd (reduction env sigma term))

let reduce env sigma = Fn.compose (reduce_econstr env sigma) EConstr.of_constr

let parse_constr_with_interp interp env sigma str =
  let vernac_str = Printf.sprintf "Check %s." str in
  match exec_get (Parse ({ontop = None}, vernac_str)) with
  | CoqAst {v = {expr = VernacCheckMayEval (_, _, constr_expr); _}; _} ->
    reduce_econstr env sigma (fst (interp env sigma ?impls:None constr_expr))
  | _ -> assert false

let parse_constr = parse_constr_with_interp Constrintern.interp_constr
let parse_type = parse_constr_with_interp Constrintern.interp_type

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

type terms =
  { levels : Constr.t Sequence.t Res.Array.t
  ; cumul : Constr.t Hash_set.t }

let take_option on seq =
  match on with
  | Some n -> Sequence.take seq n
  | None -> seq

let synthesize ~sid ~hole_type ~params ~extra_exprs ~examples ~k ~levels =
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
  | CoqEnv orig_env ->
    let orig_sigma = Evd.from_env orig_env in
    let par_env, pars = List.fold_map params ~init:orig_env
      ~f:begin fun env (param_name, param_type) ->
        let sigma = Evd.from_env env in
        let par_name = Names.Id.of_string param_name in
        let par_type = parse_type env sigma param_type in
        Environ.push_named (LocalAssum (Context.annotR par_name, par_type)) env,
        (par_name, par_type)
      end in
    let par_sigma = Evd.from_env par_env in
    let hole_ty = parse_type par_env par_sigma hole_type in
    let exs = List.map examples ~f:begin fun (inputs, output) ->
      List.map2_exn pars inputs
        ~f:(fun (name, _) inp -> name, parse_constr orig_env orig_sigma inp),
      parse_constr orig_env orig_sigma output
    end in
    let red = reduce par_env par_sigma in
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
    List.iter extra_exprs ~f:begin fun expr ->
      let j = Arguments_renaming.rename_typing par_env
        (parse_constr par_env par_sigma expr) in
      add_var j.uj_val j.uj_type
    end;
    let add_ctors ind targs =
      let packets = (Environ.lookup_mind (fst ind) par_env).mind_packets in
      for ctor_ix = 1 to Array.length packets.(snd ind).mind_consnames do
        let ctor = Constr.mkConstruct
          (Names.ith_constructor_of_inductive ind ctor_ix) in
        let j = Arguments_renaming.rename_typing par_env
          (red (Constr.mkApp (ctor, targs))) in
        add_var j.uj_val j.uj_type
      done in
    let terms = Hashtbl.create (module ConstrHash) in
    let rec synth ty n =
      let tms = Hashtbl.find_or_add terms ty
        ~default:begin fun () ->
          let tcon, targs = Constr.decompose_appvect ty in
          begin match Constr.kind tcon with
          | Ind (ind, _) -> add_ctors ind targs
          | _ -> ()
          end;
          { levels = Res.Array.empty ()
          ; cumul = Hash_set.create (module ConstrHash) }
        end in
      let len = Res.Array.length tms.levels in
      if n < len then
        Res.Array.get tms.levels n
      else
        let rec syn m =
          let level =
            begin
              if m = 0 then
                Sequence.of_list (Hashtbl.find_multi atoms ty)
              else begin
                if m > len then
                  (* Force previous levels to update cumul *)
                  Sequence.iter (syn (m - 1)) ~f:ignore;
                let open Sequence.Monad_infix in
                let prods = Sequence.unfold_step
                  ~init:begin
                    Hash_set.fold (find_returning ty)
                      ~init:Sequence.Step.Done
                      ~f:(fun step prod -> Sequence.Step.Yield (prod, step))
                  end
                  ~f:Fn.id in
                Sequence.append
                  (Sequence.range 0 (m - 1)
                    >>= fun i -> Sequence.of_list [i, m - 1; m - 1, i])
                  (Sequence.of_list [m - 1, m - 1])
                >>= begin fun (arg_lvl, prod_lvl) ->
                  prods >>= fun prod ->
                    let _, arg_ty, _ = Constr.destProd prod in
                    let arg_tms = synth arg_ty arg_lvl in
                    let prod_tms = synth prod prod_lvl in
                    arg_tms >>= fun arg_tm ->
                      prod_tms >>| fun prod_tm ->
                        red (Constr.mkApp (prod_tm, [|arg_tm|]))
                end
              end
            end
            |> Sequence.filter ~f:begin fun tm ->
              Result.is_ok (Hash_set.strict_add tms.cumul tm)
            end
            |> Sequence.memoize
            in
          Res.Array.add_one tms.levels level;
          level in
        syn n in
    let open Sequence.Monad_infix in
    Sequence.unfold_step ~init:0 ~f:(fun i -> Sequence.Step.Yield (i, i + 1))
    |> take_option levels
    >>= synth hole_ty
    |> Sequence.filter ~f:begin fun term ->
      try
        List.iter exs ~f:begin fun (subst, output) ->
          Reduction.conv orig_env (Vars.replace_vars subst term) output
        end;
        true
      with Reduction.NotConvertible ->
        false
    end
    |> take_option k
    >>| begin fun term ->
      Pp.string_of_ppcmds (Printer.pr_constr_env par_env par_sigma term)
    end
  | _ -> assert false
