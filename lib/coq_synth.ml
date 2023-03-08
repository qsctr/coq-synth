open Base
open Serapi
open Serlib
open Sertop

let debug = ref false

type example_type_target =
  | Parameter_target of Names.variable
  | Hole_target

type user_error =
  | Example_arity_error of
    { params : (Names.variable * Constr.types) list
    ; inputs : string list }
  | Example_type_error of
    { env : Environ.env
    ; judgment : Environ.unsafe_judgment
    ; target : example_type_target
    ; target_type : Constr.types
    ; subst : (Names.variable * Constr.t) list }

exception User_error of user_error

type enum_level =
  { eguess_terms : Constr.t Sequence.t
  ; mutable irefine_empty_terms : Constr.t Sequence.t option }

type term_cache_entry =
  { levels : enum_level Res.Array.t
  ; cumul : Constr.t Hash_set.t }

type ctor_type =
  { ctor : Constr.t
  ; rev_args : Constr.types list }

type rtree =
  { ty : Constr.types
  ; examples : ((Names.variable * Constr.t) list * Constr.t) list
  ; mutable terms : Constr.t Sequence.t
  ; branch : rtree_branch }
and rtree_branch =
  | EGuess
  | IRefine_ctor of { ctor : Constr.t; args : rtree list }

module ConstrHash = struct
  include Constr
  let sexp_of_t = Ser_constr.sexp_of_t
end

let take_option on seq =
  match on with
  | Some n -> Sequence.take seq n
  | None -> seq

let rec drop_prefix pre list =
  match pre, list with
  | [], _ -> Some list
  | p :: ps, x :: xs when Constr.equal p x -> drop_prefix ps xs
  | _ -> None

let string_of_user_error = function
  | Example_arity_error e ->
    Printf.sprintf
      "Number of parameters (%d) and number of inputs in example \"%s\" (%d) \
        do not match"
      (List.length e.params) (String.concat ~sep:", " e.inputs)
      (List.length e.inputs)
  | Example_type_error e ->
    let sigma = Evd.from_env e.env in
    let string_of_constr =
      Fn.compose Pp.string_of_ppcmds (Printer.pr_lconstr_env e.env sigma) in
    let target_type = string_of_constr e.target_type in
    let ety = EConstr.of_constr e.target_type in
    Printf.sprintf
      "Type of example %s (%s : %s) does not match type of %s%s"
      begin match e.target with
      | Parameter_target _ -> "input"
      | Hole_target -> "output"
      end
      (string_of_constr e.judgment.uj_val) (string_of_constr e.judgment.uj_type)
      begin match e.target with
      | Parameter_target name ->
        Printf.sprintf "parameter (%s : %s)"
          (Names.Id.to_string name) target_type
      | Hole_target -> Printf.sprintf "goal (%s)" target_type
      end
      begin
        List.filter e.subst
          ~f:(fun (name, _) -> Termops.local_occur_var sigma name ety)
        |> function
        | [] -> ""
        | occur_subst ->
          Printf.sprintf " with (%s)" @@ String.concat ~sep:", " @@
            List.map occur_subst ~f:begin fun (name, inp) ->
              Names.Id.to_string name ^ " = " ^ string_of_constr inp
            end
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
    let constr, ustate = interp env sigma ?impls:None constr_expr in
    let env' = Environ.push_context_set (UState.context_set ustate) env in
    reduce_econstr env' sigma constr, env'
  | _ -> assert false

let parse_constr = parse_constr_with_interp Constrintern.interp_constr
let parse_type = parse_constr_with_interp Constrintern.interp_type

(* let print_sexp sexp =
  Sexp.pp_hum Caml.Format.std_formatter sexp;
  Caml.Format.print_newline () *)

let with_error_handler h f =
  try f () with
  | User_error e -> h (string_of_user_error e)
  | e ->
    let bt = Caml.Printexc.get_raw_backtrace () in
    if CErrors.is_anomaly e then
      Caml.Printexc.raise_with_backtrace e bt
    else
      h (Pp.string_of_ppcmds (CErrors.print e))

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
  let ldir = Libnames.dirpath_of_string
    (if String.(logical_dir = "<>") then "" else logical_dir) in
  ignore @@ exec @@ NewDoc
    { top_name = TopLogical (Libnames.dirpath_of_string "Coq_synth")
    ; iload_path = Some begin
        Serapi_paths.coq_loadpath_default ~implicit:true
          ~coq_path:Coq_config.coqlib
          @ [ { path_spec = VoPath
                  { unix_path = physical_dir
                  ; coq_path = ldir
                  ; implicit = true
                  ; has_ml = AddNoML }
              ; recursive = true } ]
      end
    ; require_libs = None };
  let sentences = Printf.sprintf
    "Load LFindLoad. From %s Require Import %s."
    (Names.DirPath.to_string ldir) module_name in
  let sids =
    exec
      (Add ({lim = None; ontop = None; newtip = None; verb = false}, sentences))
    |> List.filter_map ~f:begin function
      | Serapi_protocol.Added (sid, _, _) -> Some sid
      | _ -> None
    end in
  List.iter sids ~f:(fun sid -> ignore (exec (Exec sid)));
  Constrextern.print_implicits := true;
  Constrextern.print_no_symbol := true;
  List.last_exn sids

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
        let par_type, env' = parse_type env sigma param_type in
        Environ.push_named
          (LocalAssum (Context.annotR par_name, par_type)) env',
        (par_name, par_type)
      end in
    let hole_ty, par_env' =
      parse_type par_env (Evd.from_env par_env) hole_type in
    let par_sigma' = Evd.from_env par_env' in
    let parse_check_ex_constr target ty subst str =
      let constr, env = parse_constr orig_env orig_sigma str in
      let j = Arguments_renaming.rename_typing env constr in
      begin
        try Reduction.conv_leq par_env' j.uj_type (Vars.replace_vars subst ty)
        with Reduction.NotConvertible ->
          raise @@ User_error
            (Example_type_error
              {env = par_env'; judgment = j; target; target_type = ty; subst})
      end;
      j.uj_val in
    let exs = List.map examples ~f:begin fun (inputs, output) ->
      List.fold2 pars inputs ~init:[] ~f:begin fun subst (name, ty) inp ->
        subst @
          [name, parse_check_ex_constr (Parameter_target name) ty subst inp]
      end
      |> function
      | Ok subst ->
        subst, parse_check_ex_constr Hole_target hole_ty subst output
      | Unequal_lengths ->
        raise (User_error (Example_arity_error {params = pars; inputs}))
    end in
    let red = reduce par_env' par_sigma' in
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
    let par_env'' = List.fold extra_exprs ~init:par_env'
      ~f:begin fun env expr ->
        let constr, env' = parse_constr env par_sigma' expr in
        let j = Arguments_renaming.rename_typing env' constr in
        add_var j.uj_val j.uj_type;
        env'
      end in
    let par_sigma'' = Evd.from_env par_env'' in
    let ctors = Hashtbl.create (module ConstrHash) in
    let decompose_prod_types ty =
      let rev_binders, ret_ty = Term.decompose_prod ty in
      List.map ~f:snd rev_binders, ret_ty in
    let infer_ctor c targs =
      let j = Arguments_renaming.rename_typing par_env''
        (red (Constr.mkApp (Constr.mkConstruct c, targs))) in
      {ctor = j.uj_val; rev_args = fst (decompose_prod_types j.uj_type)} in
    let get_ctors ty = Hashtbl.find_or_add ctors ty ~default:begin fun () ->
      let tcon, targs = Constr.decompose_appvect ty in
      match Constr.kind tcon with
      | Ind (ind, _) ->
        let consnames = (Environ.lookup_mind (fst ind) par_env'')
          .mind_packets.(snd ind).mind_consnames in
        List.init (Array.length consnames) ~f:begin fun i ->
          (* note: constructor indices start at 1 *)
          infer_ctor (Names.ith_constructor_of_inductive ind (i + 1)) targs
        end
        |> Sequence.of_list
      | _ -> Sequence.empty
    end in
    let term_cache = Hashtbl.create (module ConstrHash) in
    let lookup_cache ty =
      Hashtbl.find_or_add term_cache ty ~default:begin fun () ->
        { levels = Res.Array.empty ()
        ; cumul = Hash_set.create (module ConstrHash) }
      end in
    let dedup entry = Sequence.filter ~f:begin fun tm ->
      Result.is_ok (Hash_set.strict_add entry.cumul tm)
    end in
    let rec eguess ty n =
      let entry = lookup_cache ty in
      let len = Res.Array.length entry.levels in
      if n < len then
        (Res.Array.get entry.levels n).eguess_terms
      else
        let rec eg m =
          let terms =
            begin
              if m = 0 then begin
                Sequence.of_list (Hashtbl.find_multi atoms ty)
              end else begin
                if m > len then
                  (* extend levels to length m *)
                  ignore (eg (m - 1));
                let open Sequence.Monad_infix in
                let prods = Sequence.of_list
                  (Hash_set.to_list (find_returning ty)) in
                Sequence.append
                  (Sequence.range 0 (m - 1)
                    >>= fun i -> Sequence.of_list [i, m - 1; m - 1, i])
                  (Sequence.of_list [m - 1, m - 1])
                >>= fun (arg_lvl, prod_lvl) ->
                  prods >>= fun prod ->
                    let _, arg_ty, _ = Constr.destProd prod in
                    let arg_tms = irefine_empty arg_ty arg_lvl in
                    let prod_tms = eguess prod prod_lvl in
                    arg_tms >>= fun arg_tm ->
                      prod_tms >>| fun prod_tm ->
                        red (Constr.mkApp (prod_tm, [|arg_tm|]))
              end
            end
            |> dedup entry
            |> Sequence.memoize in
          Res.Array.add_one entry.levels
            {eguess_terms = terms; irefine_empty_terms = None};
          terms in
        eg n
    and irefine_empty ty n =
      let entry = lookup_cache ty in
      let build_terms () =
        (* extend levels to length n+1 *)
        let guess_terms = eguess ty n in
        let goal_rev_args, goal_ty = decompose_prod_types ty in
        let valid_ctors =
          Sequence.filter_map (get_ctors goal_ty) ~f:begin fun c ->
            drop_prefix goal_rev_args c.rev_args
            |> Option.map ~f:(fun rev_args' -> {c with rev_args = rev_args'})
          end in
        let ctor_terms =
          begin
            let open Sequence.Monad_infix in
            if n = 0 then
              Sequence.filter valid_ctors ~f:(fun c -> List.is_empty c.rev_args)
              >>| fun c -> c.ctor
            else
              valid_ctors >>= fun c ->
                List.rev_map c.rev_args
                  ~f:(fun arg_ty -> irefine_empty arg_ty (n - 1))
                |> Sequence.all
                >>| fun args -> red (Term.applist (c.ctor, args))
          end
          |> dedup entry in
        let terms = Sequence.memoize (Sequence.append guess_terms ctor_terms) in
        (Res.Array.get entry.levels n).irefine_empty_terms <- Some terms;
        terms in
      if n < Res.Array.length entry.levels then
        match (Res.Array.get entry.levels n).irefine_empty_terms with
        | Some terms -> terms
        | None -> build_terms ()
      else
        build_terms () in
    let rec build_rtree ty xs =
      { ty
      ; examples = xs
      ; terms = Sequence.empty
      ; branch =
        let goal_rev_args, goal_ty = decompose_prod_types ty in
        let tcon, targs = Constr.decompose_appvect goal_ty in
        match xs with
        | x :: xs' when Constr.isInd tcon -> begin
            let out_fun_kind (_, o) =
              Constr.kind (fst (Constr.decompose_app o)) in
            let same_construct c x' =
              match out_fun_kind x' with
              | Construct (c', _) -> Names.eq_constructor c c'
              | _ -> false in
            match out_fun_kind x with
            | Construct (c, _) when List.for_all xs' ~f:(same_construct c) ->
              let c_type = infer_ctor c targs in
              IRefine_ctor
                { ctor = c_type.ctor
                ; args =
                  Option.value_exn (drop_prefix goal_rev_args c_type.rev_args)
                  |> List.rev
                  |> List.mapi ~f:begin fun i arg_ty ->
                    build_rtree arg_ty @@
                      List.map xs ~f:begin fun (subst, o) ->
                        subst, (snd (Constr.destApp o)).(Array.length targs + i)
                      end
                  end }
            | _ -> EGuess
          end
        | _ -> EGuess
      } in
    let rec irefine_rtree rt n =
      let guess_terms =
        Sequence.filter (eguess rt.ty n) ~f:begin fun term ->
          try
            List.iter rt.examples ~f:begin fun (subst, output) ->
              Reduction.conv orig_env (Vars.replace_vars subst term) output
            end;
            true
          with Reduction.NotConvertible ->
            false
        end in
      let ctor_terms =
        begin
          match rt.branch with
          | EGuess -> Sequence.empty
          | IRefine_ctor c ->
            match c.args with
            | [] when n = 0 -> Sequence.singleton c.ctor
            | _ ->
              let open Sequence.Monad_infix in
              List.map c.args ~f:begin fun sub_rt ->
                (* important: evaluate this first *)
                let prev_terms = sub_rt.terms in
                [prev_terms; irefine_rtree sub_rt n]
              end
              |> List.all
              |> List.tl_exn (* drop all-prev args *)
              |> Sequence.of_list
              >>= fun multi_args ->
                Sequence.all multi_args
                >>| fun args -> red (Term.applist (c.ctor, args))
        end in
      let new_terms =
        Sequence.memoize (Sequence.append guess_terms ctor_terms) in
      rt.terms <- Sequence.memoize (Sequence.append rt.terms new_terms);
      new_terms in
    let synth =
      match exs with
      | [] -> irefine_empty hole_ty
      | _ -> irefine_rtree (build_rtree hole_ty exs) in
    let open Sequence.Monad_infix in
    Sequence.unfold ~init:0 ~f:(fun i -> Some (i, i + 1))
    |> take_option levels
    >>= synth
    |> take_option k
    >>| begin fun term ->
      Pp.string_of_ppcmds (Printer.pr_constr_env par_env'' par_sigma'' term)
    end
  | _ -> assert false
