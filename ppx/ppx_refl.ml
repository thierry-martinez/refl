open Common

(*
let attr_nobuiltin : (Ppxlib.core_type, unit -> unit) Ppxlib.Attribute.t =
  Ppxlib.Attribute.declare "refl.nobuiltin" Core_type
    (Ppxlib.Ast_pattern.(pstr nil))
    Fun.id

let attr_opaque : (Ppxlib.core_type, unit -> unit) Ppxlib.Attribute.t =
  Ppxlib.Attribute.declare "refl.opaque" Core_type
    (Ppxlib.Ast_pattern.(pstr nil))
    Fun.id
*)

let map_lident f (ident : Longident.t) : Longident.t =
  match ident with
  | Ldot (prefix, name) -> Ldot (prefix, f name)
  | Lident ident -> Lident (f ident)
  | _ -> assert false

let rec remove_ident_prefix_opt (prefix : Longident.t) (ident : Longident.t)
    : Longident.t option =
  match ident with
  | Ldot (prefix', name) ->
      if prefix = prefix' then
        Some (Lident name)
      else
        Option.map (fun new_prefix -> Longident.Ldot (new_prefix, name))
          (remove_ident_prefix_opt prefix prefix')
  | Lapply (a, b) ->
      begin match
        a, remove_ident_prefix_opt prefix a,
        b, remove_ident_prefix_opt prefix b
      with
      | _, Some a, _, Some b
      | a, None, _, Some b
      | _, Some a, b, None -> Some (Lapply (a, b))
      | _, None, _, None -> None
      end
  | Lident _ -> None

let ident_of_str (x : Ast_helper.str) : Ppxlib.expression =
  Ppxlib.Ast_helper.Exp.ident ~loc:x.loc (Metapp.lid_of_str x)

let item i =
  Printf.sprintf "item%d" i

let rec iterate acc f i =
  if i > 0 then
    iterate (f acc) f (pred i)
  else
    acc

let rec iterate_i_aux acc f i j =
  if i < j then
    iterate_i_aux (f i acc) f (succ i) j
  else
    acc

let iterate_i acc f i =
  iterate_i_aux acc f 0 i

let peano_type_of_int i =
  iterate [%type: [`Zero]] (fun t -> [%type: [`Succ of [%t t]]]) i

let refl_dot field : Longident.t =
  Ldot (Lident "Refl", field)

let rec cut l =
  match l with
  | even :: odd :: tail ->
      let even_tail, odd_tail = cut tail in
      even :: even_tail, odd :: odd_tail
  | [even] -> [even], []
  | [] -> [], []

let rec binary_of_int zero one final i length =
  if length > 1 then
    if i mod 2 = 0 then
      zero (binary_of_int zero one final (i / 2) ((length + 1) / 2))
    else
      one (binary_of_int zero one final (i / 2) (length - (length + 1) / 2))
  else
    final

let binary_type_of_int i length =
  binary_of_int
    (fun tail k -> tail [%type: [`Zero of [%t k]]])
    (fun tail k -> tail [%type: [`One of [%t k]]])
    Fun.id
    i length
    [%type: [`Start]]

module ReflValue (Value : Metapp.ValueS) = struct
  include Value

  let peano_of_int zero succ i =
    iterate zero (fun arg -> construct succ [arg]) i

  let typed_vector_of_list nil cons l =
    let add_item item acc =
      construct cons [record [
         Lident "head", item;
         Lident "tail", acc]] in
    List.fold_right add_item l nil

  let sequence_of_list l =
    let add_item item acc =
      tuple [item; acc] in
    List.fold_right add_item l (construct (Lident "()") [])

  let tnil = refl_dot "TNil"

  let tcons = refl_dot "TCons"

  let tuple_of_list l =
    typed_vector_of_list (construct tnil []) tcons l

  let rnil = refl_dot "RNil"

  let rcons = refl_dot "RCons"

  let record_of_list l =
    typed_vector_of_list (construct rnil []) rcons l

  let cnode = refl_dot "CNode"

  let cleaf = refl_dot "CLeaf"

  let rec binary_choices_of_list l =
    match l with
    | [] -> assert false
    | [leaf] ->
        construct cleaf [leaf]
    | _ ->
        let even, odd = cut l in
        construct cnode [record [
          (Lident "zero", binary_choices_of_list even);
          (Lident "one", binary_choices_of_list odd)]]

  let vcnil = refl_dot "VCNil"

  let vccons = refl_dot "VCCons"

  let variant_choices_of_list l =
    typed_vector_of_list (construct vcnil []) vccons l

  let onil = refl_dot "ONil"

  let ocons = refl_dot "OCons"

  let object_methods_of_list l =
    typed_vector_of_list (construct onil []) ocons l

  let vnil = refl_dot "VNil"

  let vcons = refl_dot "VCons"

  let vector_of_list l =
    typed_vector_of_list (construct vnil []) vcons l

  let sfirst = refl_dot "Start"

  let snext = refl_dot "Next"

  let selection_of_int i =
    peano_of_int (construct sfirst []) snext i

  let vfirst = refl_dot "VFirst"

  let vnext = refl_dot "VNext"

  let variable_of_int i =
    peano_of_int (construct vfirst []) vnext i

  let cfirst = refl_dot "CFirst"

  let cnext = refl_dot "CNext"

  let choice_of_int i sequence =
    peano_of_int (construct cfirst [sequence]) cnext i

  let cend = refl_dot "CEnd"

  let czero = refl_dot "CZero"

  let cone = refl_dot "COne"

  let binary_choice_of_int i length sequence =
    binary_of_int
      (fun tail -> construct czero [tail])
      (fun tail -> construct cone [tail])
      (construct cend [sequence])
      i length

  let binary_start = refl_dot "BinaryStart"

  let zero = refl_dot "Zero"

  let one = refl_dot "One"

  let select = refl_dot "Select"

  let binary_selection_of_int i length =
    binary_of_int
      (fun tail k -> tail (construct zero [k]))
      (fun tail k -> tail (construct one [k]))
      (fun k -> construct select [k])
      i length
      (construct binary_start [])

  let s_zero = refl_dot "Zero"

  let s_succ = refl_dot "Succ"

  let length_of_int i =
    peano_of_int (construct s_zero []) s_succ i

  let s_nil = refl_dot "Nil"

  let s_append = refl_dot "Add"

  let append_of_int i =
    peano_of_int (construct s_nil []) s_append i

  let vtanil = refl_dot "VTANil"

  let vtacons = refl_dot "VTACons"

  let transfer_arguments_of_list l =
    typed_vector_of_list (construct vtanil []) vtacons l

  let vtnil = refl_dot "VTNil"

  let vtcons = refl_dot "VTCons"

  let transfer_of_list l =
    typed_vector_of_list (construct vtnil []) vtcons l

  let enil = refl_dot "ENil"

  let econs = refl_dot "ECons"

  let equalities_of_list l =
    typed_vector_of_list (construct enil []) econs l
end

let append_type_sequence_of_list l e =
  List.fold_right (fun ty acc -> [%type: [%t ty] * [%t acc]]) l e

let type_sequence_of_list l =
  append_type_sequence_of_list l [%type: unit]

let rec binary_type_of_list l =
  match l with
  | [] -> [%type: unit]
  | [leaf] -> [%type: [%t leaf] ref]
  | _ ->
      let even, odd = cut l in
      [%type: [%t binary_type_of_list even] * [%t binary_type_of_list odd]]

type type_info = {
    desc_name : string;
    arity : int;
    td : Ppxlib.type_declaration;
    recursive : Ppxlib.Asttypes.rec_flag ref;
  }

let refl_name s =
  s ^ "_refl"

let structure_name s =
  s ^ "__structure"

let rec_group_name s =
  s ^ "__rec_group"

let arity_name s =
  s ^ "__arity"

let kinds_name s =
  s ^ "__kinds"

let gadt_name s =
  s ^ "__gadt"

let type_refl_ctor s =
  "Refl_" ^ s

type type_names = {
     refl : string;
     structure : string;
     rec_group : string;
     arity : string;
     kinds : string;
     gadt : string;
     refl_ctor : string;
   }

let type_names_of_type_name type_name = {
     refl = refl_name type_name;
     structure = structure_name type_name;
     rec_group = rec_group_name type_name;
     arity = arity_name type_name;
     kinds = kinds_name type_name;
     gadt = gadt_name type_name;
     refl_ctor = type_refl_ctor type_name;
   }

let type_info_of_type_declaration recursive (td : Ppxlib.type_declaration) =
  { td;
    desc_name = refl_name td.ptype_name.txt;
    arity = List.length td.ptype_params;
    recursive;
  }

type free_variable = {
    index : int;
    name : string;
    mutable bound : bool;
  }

module StringIndexer = Indexer.Make (String)

type context = {
    name : string option;
    rec_types : (int * int * type_info) StringMap.t option;
    vars : StringIndexer.t;
    fresh_counter : int ref;
    free_var_table : free_variable StringHashtbl.t;
    free_vars : free_variable list ref;
    rec_type_refs : IntSet.t ref;
    constraints : Constraints.t ref;
    origin : Constraints.Variables.Path.origin;
    selector : Constraints.Variables.Path.selector;
    rev_eqs : Ppxlib.core_type list ref;
    eqs_counter : int ref;
    type_names : type_names;
    type_args : string list;
    type_vars : Ppxlib.core_type list;
    type_expr : Ppxlib.core_type;
    exists : Constraints.Transfer.t option ref;
    gadt_args : Ppxlib.core_type list;
    original_vars : Ppxlib.core_type list;
  }

let var_of_core_type_opt (ty : Ppxlib.core_type) =
  match ty with
  | [%type: _] -> Some None
  | { ptyp_desc = Ptyp_var s; _ } -> Some (Some s)
  | _ -> None

let var_of_core_type (ty : Ppxlib.core_type) =
  match var_of_core_type_opt ty with
  | Some var -> var
  | None ->
      Location.raise_errorf ~loc:!Ast_helper.default_loc
        "Type variable expected but '%a' found" Ppxlib.Pprintast.core_type ty

let make_index (f : 'a -> string option) (l : 'a list) (count : int) :
    (int * int * 'a) StringMap.t =
  let add_type_arg i acc arg =
    let acc =
      match f arg with
      | None -> acc
      | Some var -> StringMap.add var (i, count, arg) acc in
    acc in
  ListExt.fold_lefti add_type_arg StringMap.empty l

let type_arg i =
   Printf.sprintf "a%d" i

let type_constr_of_string ?(args = []) s =
  Ppxlib.Ast_helper.Typ.constr (Metapp.mkloc (Longident.Lident s)) args

let make_context ?name rec_types original_vars vars =
  let type_args = List.init (StringIndexer.count vars) type_arg in
  let type_vars = List.map Ppxlib.Ast_helper.Typ.var type_args in
  let name_default = Option.value ~default:"" name in
  let type_expr = type_constr_of_string name_default ~args:type_vars in
  { name;
    rec_types;
    vars;
    fresh_counter = ref 0;
    free_var_table = StringHashtbl.create 7;
    free_vars = ref [];
    rec_type_refs = ref IntSet.empty;
    constraints = ref Constraints.bottom;
    origin = [];
    selector = Direct;
    rev_eqs = ref [];
    eqs_counter = ref 0;
    type_names = type_names_of_type_name name_default;
    type_args;
    type_vars;
    type_expr;
    exists = ref None;
    gadt_args = type_vars;
    original_vars;
  }

let context_of_type_declaration (td : Ppxlib.type_declaration) rec_types
    : context =
  let vars =
    StringIndexer.of_list
      (td.ptype_params |> List.map (fun (ty, _) -> var_of_core_type ty)) in
  make_context ~name:td.ptype_name.txt rec_types (List.map fst td.ptype_params)
    vars

let builtins_dot field : Longident.t =
  Ldot (refl_dot "Builtins", field)

let irrefutable () =
  [Ppxlib.Ast_helper.Exp.case [%pat? _] (Ppxlib.Ast_helper.Exp.unreachable ())]

let structure_of_tuple structure_of_type context
    (types : Ppxlib.core_type list)
    : Ppxlib.core_type * Ppxlib.expression =
  let arity = List.length types in
  let types, descs =
    List.split (List.map (structure_of_type context) types) in
  let module Values (Value : Metapp.ValueS) = struct
    include ReflValue (Value)
    let items = List.init arity (fun i -> var (item i))
    let sequence = sequence_of_list items
    let tuple = tuple items
  end in
  let module ValuesExp = Values (Metapp.Exp) in
  let module ValuesPat = Values (Metapp.Pat) in
  let construct =
    Ppxlib.Ast_helper.Exp.case ValuesPat.sequence ValuesExp.tuple :: irrefutable () in
  let destruct = Ppxlib.Ast_helper.Exp.case ValuesPat.tuple ValuesExp.sequence in
  [%type: [`Tuple of [%t type_sequence_of_list types]]],
  [%expr Refl.Tuple {
    structure = [%e ValuesExp.tuple_of_list descs];
    construct = [%e Ppxlib.Ast_helper.Exp.function_ construct];
    destruct = [%e Ppxlib.Ast_helper.Exp.function_ [destruct]];
  }]

let rec for_alli_from index p list =
  match list with
  | [] -> true
  | hd :: tl -> p index hd && for_alli_from (succ index) p tl

let for_alli p list =
  for_alli_from 0 p list

let type_args_regular context (args : Ppxlib.core_type list) =
  List.length args = StringIndexer.count context.vars &&
  args |> for_alli begin fun i (arg : Ppxlib.core_type) ->
    match arg with
    | { ptyp_desc = Ptyp_var s; _ } ->
        begin match StringIndexer.find_opt s context.vars with
        | Some j -> i = j
        | None -> false
        end
    | _ -> false
  end

(*
let lzero = refl_dot "LZero"

let lsucc = refl_dot "LSucc"

let sequence_length_of_int i =
  peano_of_int (construct lzero) lsucc i
*)

(*
let anil = refl_dot "ANil"

let acons = refl_dot "ACons"

let rec_group_of_list l =
  typed_vector_of_list (construct anil) acons l
*)

let make_transfer present unknown compose
    (transfer : Constraints.Variables.transfer) =
  match transfer with
  | Present -> present
  | Depend depend ->
      let add_depend unknown longident_list =
        let add_longident present txt =
          compose txt present unknown in
        List.fold_left add_longident present longident_list in
      List.fold_left add_depend unknown depend

let compose_transfer txt present unknown =
  Constraints.Transfer.Constr (txt, present, unknown)

let compose_type txt present unknown =
  Ppxlib.Ast_helper.Typ.constr (Metapp.mkloc txt) [present; unknown]

let compose_expr txt present unknown =
  [%expr [%e Ppxlib.Ast_helper.Exp.ident (Metapp.mkloc txt)]
     [%e present] [%e unknown]]

let variable_types type_name arity name absent =
  type_sequence_of_list (List.init arity begin fun i ->
    Ppxlib.Ast_helper.Typ.constr
      (Metapp.mkloc (subst_ident (fun s -> name s i) type_name))
      [[%type: [`Present]]; absent i]
  end)

module ReflValueExp = ReflValue (Metapp.Exp)

module ReflValuePat = ReflValue (Metapp.Pat)

module ReflValueVal = ReflValue (Metapp.Value)

let subst_free_variables
    (f : Location.t -> string option -> Ppxlib.core_type)
    (ty : Ppxlib.core_type) : Ppxlib.core_type =
  let mapper = object
    inherit Ppxlib.Ast_traverse.map as super

    method! core_type (ty : Ppxlib.core_type) : Ppxlib.core_type =
      match var_of_core_type_opt ty with
      | None -> super#core_type ty
      | Some var -> f ty.ptyp_loc var
  end in
  mapper#core_type ty

exception Exists of Location.t * string option

let () =
  Printexc.register_printer (fun exc ->
    match exc with
    | Exists (loc, name) ->
        Some (Format.asprintf "@[Exists@ (@[%a@],@[%a@])@]"
          Location.print_loc loc (Format.pp_print_option Format.pp_print_string)
          name)
    | _ -> None)

let subst_type_vars_opt map _loc name =
  Option.bind name @@ fun name ->
  Option.bind (StringMap.find_opt name map) @@ fun index ->
  Some (Ppxlib.Ast_helper.Typ.var (type_arg index))

let subst_type_vars map loc name =
  match subst_type_vars_opt map loc name with
  | None -> raise (Exists (loc, name))
  | Some result -> result

(*
let subst_type_vars_exists map loc name =
  match subst_type_vars_opt map loc name with
  | None -> Ppxlib.Ast_helper.Typ.any ()
  | Some result -> result
*)

let instantiate_with_free accu map _loc name =
  match name with
  | None -> invalid_arg "subst_type_vars_with_free"
  | Some name ->
      match StringMap.find_opt name map with
      | Some index -> type_constr_of_string (type_arg index)
      | None ->
          accu |> Metapp.mutate (StringSet.add name);
          type_constr_of_string name

let instantiate _loc var =
  match var with
  | None -> failwith "Not implemented: instantiate"
  | Some var -> type_constr_of_string var

let structure_of_constr structure_of_type context ?rec_type
    (constr : Longident.t) (args : Ppxlib.core_type list)
    : Ppxlib.core_type * Ppxlib.expression =
  let t, desc =
    match rec_type with
    | None ->
        context.constraints |> Metapp.mutate (
          Constraints.add_inherited_kind (subst_ident kinds_name constr));
        let structure =
          Ppxlib.Ast_helper.Typ.constr
            (Metapp.mkloc (subst_ident structure_name constr))
            [] in
        let rec_group_type =
          Ppxlib.Ast_helper.Typ.constr
            (Metapp.mkloc (subst_ident rec_group_name constr))
            [] in
        let unwrapped_desc =
          Ppxlib.Ast_helper.Exp.ident
            (Metapp.mkloc (subst_ident refl_name constr)) in
        let t, desc =
          [%type: [`RecGroup of [%t structure] * [%t rec_group_type]]],
          [%expr RecGroup { desc = [%e unwrapped_desc](*;
            rec_group = [%e rec_group_expr] *)}] in
        let arrow =
          [%type: [%t type_constr_of_string context.type_names.gadt
             ~args:context.gadt_args] ->
          [%t Ppxlib.Ast_helper.Typ.constr
            (Metapp.mkloc (subst_ident gadt_name constr)) args]] in
        [%type: [`SubGADT of [%t t]]],
        [%expr Refl.SubGADT ([%e desc] : [%t arrow])]
    | Some (index, length, { desc_name; recursive; _ }) ->
        recursive := Recursive;
        let arrow =
          [%type: [%t type_constr_of_string context.type_names.gadt
             ~args:context.gadt_args] ->
          [%t Ppxlib.Ast_helper.Typ.constr
            (Metapp.mkloc (subst_ident gadt_name constr)) args]] in
        context.rec_type_refs |> Metapp.mutate (IntSet.add index);
        [%type: [`SubGADT of [`Rec of [%t binary_type_of_int index length]]]],
        [%expr Refl.SubGADT (Refl.Rec {
          index = [%e ReflValueExp.binary_selection_of_int index length];
          desc = [%e ident_of_str (Metapp.mkloc desc_name)]} :
          [%t arrow])] in
(*
  let t, desc =
    match rec_type with
    | Some _ -> t, desc
    | None ->
        begin
            let ty =
              Ppxlib.Ast_helper.Typ.constr (Metapp.mkloc (subst_ident gadt_name constr))
                args in
            let ty =
              subst_free_variables (subst_type_vars_exists context.vars.map) ty in
            let eq_index = !(context.eqs_counter) in
            context.eqs_counter := succ eq_index;
            context.rev_eqs := ty :: !(context.rev_eqs);
            [%type: [`SelectGADT of [%t t] * [%t peano_type_of_int eq_index]]],
            [%expr Refl.SelectGADT {
              index = [%e ReflValueExp.selection_of_int (succ eq_index)];
              desc = [%e desc]
            }]
        end in
*)
  let t, desc =
    if type_args_regular context args &&
      match context.name with
      | None -> true
      | Some name -> constr = Lident name then
      begin
        if rec_type = None then
          context.constraints |> Metapp.mutate (fun constraints ->
            args |> ListExt.fold_lefti
              (fun i (constraints : Constraints.t) arg ->
                Constraints.add_variable i ([(constr, i)], Direct) constraints)
              constraints);
        t, desc
      end
    else
      let args = args |> List.map begin fun arg ->
        let old_ref = context.constraints in
        let old_kinds, old_variables = !old_ref in
        let constraints' = ref (old_kinds, Constraints.Variables.bottom) in
        let context = { context with
          constraints = constraints';
          origin = [];
          selector = Direct; } in
        let structure = structure_of_type context arg in
        let kinds, variables = !constraints' in
        old_ref := (kinds, old_variables);
        structure, variables
      end in
      let args, variables = List.split args in
      let args_type, args_expr = List.split args in
      let args_type = type_sequence_of_list args_type in
      let transfer_arguments transfer =
        ReflValueExp.transfer_arguments_of_list
          (List.init (StringIndexer.count context.vars) transfer) in
      let transfer_matrix variables =
        let transfer_positive =
          transfer_arguments begin fun j ->
            Constraints.Variables.make_transfer variables Right j |>
            make_transfer [%expr Refl.Transfer] [%expr Refl.Skip] compose_expr
          end in
        let transfer_negative =
          transfer_arguments begin fun j ->
            Constraints.Variables.make_transfer variables Left j |>
            make_transfer [%expr Refl.Transfer] [%expr Refl.Skip] compose_expr
          end in
        let transfer_direct =
          transfer_arguments begin fun j ->
            Constraints.Variables.make_transfer variables Direct j |>
            make_transfer [%expr Refl.Transfer] [%expr Refl.Skip] compose_expr
          end in
        [%expr {
          pp = [%e transfer_positive];
          pn = [%e transfer_negative];
          np = [%e transfer_negative];
          nn = [%e transfer_positive];
        }, [%e transfer_direct]] in
      let transfer =
        ReflValueExp.transfer_of_list (List.map transfer_matrix variables) in
      let args_count = List.length args in
      let skip_item name i  =
        [%expr fun () -> [%e
          Ppxlib.Ast_helper.Exp.ident (Metapp.mkloc (map_lident
            (fun constr -> name constr i) constr))] Refl.VKeep Refl.VSkip] in
      let make_skip_vector list =
        ReflValueExp.typed_vector_of_list
          (ReflValueExp.construct (refl_dot "SKNil") []) (refl_dot "SKCons")
          list in
      let skip_positive =
        make_skip_vector (List.init args_count (fun i ->
          skip_item Constraints.Variables.positive_name i)) in
      let skip_negative =
        make_skip_vector (List.init args_count (fun i ->
          skip_item Constraints.Variables.negative_name i)) in
      let skip_direct =
        make_skip_vector (List.init args_count (fun i ->
          skip_item Constraints.Variables.direct_name i)) in
      let transfer =
        [%expr Transfer_skip {
          transfer_vector = [%e transfer];
          skip_positive = [%e skip_positive];
          skip_negative = [%e skip_negative];
          skip_direct = [%e skip_direct]}] in
      let nb_args = List.length args in
      let variable_types name =
        variable_types constr nb_args name
          (fun _ -> [%type: [`Absent]]) in
      let subpositive = variable_types Constraints.Variables.positive_name in
      let subnegative = variable_types Constraints.Variables.negative_name in
      let subdirect = variable_types Constraints.Variables.direct_name in
      let arity = StringIndexer.count context.vars in
      let arguments = type_sequence_of_list (variables |> List.map begin
        fun variables ->
          let argument_positive =
            type_sequence_of_list (List.init arity begin fun j ->
              Constraints.Variables.make_transfer variables Right j |>
              make_transfer [%type: [`Present]] [%type: [`Absent]] compose_type
            end) in
          let argument_negative =
            type_sequence_of_list (List.init arity begin fun j ->
              Constraints.Variables.make_transfer variables Left j |>
              make_transfer [%type: [`Present]] [%type: [`Absent]] compose_type
            end) in
          let argument_direct =
            type_sequence_of_list (List.init arity begin fun j ->
              Constraints.Variables.make_transfer variables Direct j |>
              make_transfer [%type: [`Present]] [%type: [`Absent]] compose_type
            end) in
          [%type: [%t argument_positive] * [%t argument_negative] *
             [%t argument_direct]]
      end) in
      let t =
        [%type: [`Apply of [%t t] * [%t args_type] * [%t subpositive]
          * [%t subnegative] * [%t subdirect] * [%t arguments]]] in
      let desc =
        [%expr Refl.Apply {
          arguments = [%e ReflValueExp.vector_of_list args_expr];
          desc = [%e desc];
          transfer = [%e transfer];
         }] in
      if rec_type = None then
        context.constraints |> Metapp.mutate (fun constraints ->
          variables |> ListExt.fold_lefti
            (fun i (constraints : Constraints.t) variables ->
              IntMap.fold (fun j path_set constraints ->
                Constraints.Variables.PathSet.fold (fun (origin, selector) ->
                  let origin = (constr, i) :: origin in
                  Constraints.add_variable j (origin, selector)) path_set
                  constraints)
                variables constraints)
            constraints);
      t, desc in
  t, desc

let expr_of_string s =
  Ppxlib.Ast_helper.Exp.constant (Ppxlib.Ast_helper.Const.string s)

let structure_of_row_field structure_of_type context
    (row_field : Ppxlib.row_field)
    : Ppxlib.core_type * Ppxlib.expression =
  Ppxlib.Ast_helper.with_default_loc (Metapp.Rf.to_loc row_field) @@ fun () ->
  match Metapp.Rf.destruct row_field with
  | Rtag (label, _, args) ->
      let structure, desc =
        match args with
        | [] -> [%type: unit], [%expr VNone]
        | arg :: _ ->
            let structure, desc = structure_of_type context arg in
            [%type: [%t structure] * unit], [%expr VSome [%e desc]] in
      [%type: [`Constr of [%t structure]]],
      [%expr Refl.VConstructor {
        name = [%e expr_of_string label.txt];
        argument = [%e desc]}]
  | Rinherit ty ->
      let structure, desc = structure_of_type context ty in
      [%type: [`Inherit of [%t structure]]],
      [%expr Refl.VInherit [%e desc]]

let accessors_of_row_field (ty : Ppxlib.core_type Lazy.t) i
    (row_field : Ppxlib.row_field)
    : Ppxlib.case * Ppxlib.case =
  let arg = "arg" in
  Ppxlib.Ast_helper.with_default_loc (Metapp.Rf.to_loc row_field) @@ fun () ->
  let module Values (Value : Metapp.ValueS) = struct
    include ReflValue (Value)
    let sequence, variant =
      match Metapp.Rf.destruct row_field with
      | Rtag (label, _, []) ->
          sequence_of_list [], variant label.txt None
      | Rtag (label, _, _) ->
          let ident = var arg in
          sequence_of_list [ident], variant label.txt (Some ident)
      | Rinherit { ptyp_desc = Ptyp_constr (type_name, _); _ } ->
          let pat () =
            Ppxlib.Ast_helper.Pat.alias
              (Ppxlib.Ast_helper.Pat.type_ type_name) (Metapp.mkloc arg) in
          let expr () =
            [%expr ([%e ReflValueExp.var arg] :> [%t Lazy.force ty])] in
          var arg, choice expr pat
      | _ ->
          Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc
            "refl cannot be derived for such polymorphic variants"
    let choice = choice_of_int i sequence
  end in
  let module ValuesExp = Values (Metapp.Exp) in
  let module ValuesPat = Values (Metapp.Pat) in
  Ppxlib.Ast_helper.Exp.case ValuesPat.choice ValuesExp.variant,
  Ppxlib.Ast_helper.Exp.case ValuesPat.variant ValuesExp.choice

let structure_of_variant structure_of_type context
    (fields : Ppxlib.row_field list)
    : Ppxlib.core_type * Ppxlib.expression =
  let cases =
    List.map (structure_of_row_field structure_of_type context) fields in
  let types, descs = List.split cases in
  let ty = lazy begin
    let fields = fields |> List.map begin fun (field : Ppxlib.row_field) ->
      match Metapp.Rf.destruct field with
      | Rtag (label, _, list) ->
          let list =
            match list with
            | [] -> []
            | _ :: _ -> [[%type: _]] in
          Metapp.Rf.tag label false list
      | Rinherit _ -> field
    end in
    Ppxlib.Ast_helper.Typ.variant fields Closed None
  end in
  let accessors = List.mapi (accessors_of_row_field ty) fields in
  let construct, destruct = List.split accessors in
  let construct = construct @ irrefutable () in
  [%type: [`Variant of [%t type_sequence_of_list types]]],
  [%expr Refl.Variant {
    constructors = [%e ReflValueExp.variant_choices_of_list descs];
    construct = [%e Ppxlib.Ast_helper.Exp.function_ construct];
    destruct = [%e Ppxlib.Ast_helper.Exp.function_ destruct];
  }]

let structure_of_builtins_or_constr structure_of_type context
    (ty : Ppxlib.core_type)
    (constr : Longident.t) (args : Ppxlib.core_type list)
    : Ppxlib.core_type * Ppxlib.expression =
  let ty =
    match ty.ptyp_desc with
    | Ptyp_constr (lid, args) ->
        begin match remove_ident_prefix_opt (Lident "Stdlib") lid.txt with
        | None -> ty
        | Some txt ->
            { ty with ptyp_desc = Ptyp_constr ({ lid with txt }, args)}
        end
    | _ -> ty in
  match { ty with ptyp_attributes = [] } with
  | [%type: bool] | [%type: Bool.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Bool");
      [%type: [`Builtin of [`Bool]]], [%expr Refl.Builtin Refl.Bool]
  | [%type: bytes] | [%type: Bytes.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Bytes");
      [%type: [`Builtin of [`Bytes]]], [%expr Refl.Builtin Refl.Bytes]
  | [%type: char] | [%type: Char.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Char");
      [%type: [`Builtin of [`Char]]], [%expr Refl.Builtin Refl.Char]
  | [%type: float] | [%type: Float.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Float");
      [%type: [`Builtin of [`Float]]], [%expr Refl.Builtin Refl.Float]
  | [%type: int] | [%type: Int.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Int");
      [%type: [`Builtin of [`Int]]], [%expr Refl.Builtin Refl.Int]
  | [%type: int32] | [%type: Int32.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Int32");
      [%type: [`Builtin of [`Int32]]], [%expr Refl.Builtin Refl.Int32]
  | [%type: int64] | [%type: Int64.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Int64");
      [%type: [`Builtin of [`Int64]]], [%expr Refl.Builtin Refl.Int64]
  | [%type: nativeint] | [%type: Nativeint.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Nativeint");
      [%type: [`Builtin of [`Nativeint]]], [%expr Refl.Builtin Refl.Nativeint]
  | [%type: string] | [%type: String.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "String");
      [%type: [`Builtin of [`String]]], [%expr Refl.Builtin Refl.String]
  | [%type: unit] ->
      structure_of_constr structure_of_type context (builtins_dot "unit") args
  | [%type: [%t? subtype] array] | [%type: [%t? subtype] Array.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Array");
      let structure, desc = structure_of_type context subtype in
      [%type: [`Array of [%t structure]]], [%expr Array [%e desc]]
  | [%type: [%t? _] list] | [%type: [%t? _] List.t] ->
      structure_of_constr structure_of_type context (builtins_dot "list") args
  | [%type: ([%t? _], [%t? _]) result] | [%type: ([%t? _], [%t? _]) Result.t ]->
      structure_of_constr structure_of_type context (builtins_dot "result") args
  | [%type: [%t? _] option] | [%type: [%t? _] Option.t] ->
      structure_of_constr structure_of_type context (builtins_dot "option") args
  | [%type: [%t? _] ref] ->
      structure_of_constr structure_of_type context (builtins_dot "ref") args
  | [%type: [%t? ty] Lazy.t] ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Lazy");
      let ty, desc = structure_of_type context ty in
      [%type: [`Lazy of [%t ty]]], [%expr Refl.Lazy [%e desc]]
  | _ ->
      structure_of_constr structure_of_type context constr args

let find_rec_type context constr =
  match context.rec_types, constr with
  | Some rec_types, Longident.Lident name ->
      StringMap.find_opt name rec_types
  | _ -> None

let free_variable context =
  let index = !(context.fresh_counter) in
  context.fresh_counter := succ index;
  let var = { index; name = Printf.sprintf "free%d" index; bound = false } in
  context.free_vars := var :: !(context.free_vars);
  var

let name_free_variable context s =
  match StringHashtbl.find_opt context.free_var_table s with
  | Some var -> var
  | None ->
      let var = free_variable context in
      StringHashtbl.add context.free_var_table s var;
      var

let structure_of_arrow structure_of_type context
    (label : Ppxlib.Asttypes.arg_label)
    parameter result =
  let label_desc =
    match label with
    | Nolabel -> None
    | Labelled s -> Some (false, s)
    | Optional s -> Some (true, s) in
  let parameter =
    match label with
    | Nolabel | Labelled _ -> parameter
    | Optional _ -> [%type: [%t parameter] option] in
  let parameter_structure, parameter_desc =
    let context = { context with
      selector = Constraints.Variables.Path.left context.selector } in
    structure_of_type context parameter in
  let result_structure, result_desc =
    let context = { context with
      selector = Constraints.Variables.Path.right context.selector } in
    structure_of_type context result in
  begin match label_desc with
  | None ->
      [%type: [`Arrow of [%t parameter_structure] -> [%t result_structure]]],
      [%expr Refl.Arrow {
        parameter = [%e parameter_desc];
        result = [%e result_desc];
      }]
  | Some (optional, s) ->
      [%type: [`LabelledArrow of
        [%t parameter_structure] -> [%t result_structure]]],
      [%expr Refl.LabelledArrow {
        label = [%e expr_of_string s];
        optional = [%e
          if optional then
            [%expr true]
          else
            [%expr false]];
        parameter = [%e parameter_desc];
        result = [%e result_desc];
        wrap =
          (fun f -> [%e Ppxlib.Ast_helper.Exp.fun_ label None [%pat? x] [%expr f x]]);
        unwrap =
          (fun f x -> [%e Ppxlib.Ast_helper.Exp.apply [%expr f] [label, [%expr x]]]);
      }]
  end

let structure_of_object_field structure_of_type context
    (object_field : Metapp.Of.t)
    : (Ppxlib.core_type * Ppxlib.expression) *
    ((Ppxlib.pattern * Ppxlib.class_field) * Ppxlib.expression) =
  let loc = Metapp.Of.to_loc object_field in
  Ppxlib.Ast_helper.with_default_loc loc @@ fun () ->
  match Metapp.Of.destruct object_field with
  | Otag (label, argument) ->
      let structure, desc = structure_of_type context argument in
      let structure =
        [%type: [`Method of [%t structure]]],
        [%expr Refl.OMethod {
          name = [%e expr_of_string label.txt];
          desc = [%e desc]}] in
      let construct =
        ((Ppxlib.Ast_helper.Pat.var label,
          Ppxlib.Ast_helper.Cf.method_ label Public
           (Ppxlib.Ast_helper.Cf.concrete Fresh [%expr
             [%e Ppxlib.Ast_helper.Exp.ident (Metapp.lid_of_str label)] ()])),
          [%expr fun () -> [%e Metapp.Exp.send [%expr c] label]]) in
      structure, construct
  | Oinherit _ ->
      Location.raise_errorf ~loc
        "ppx_refl does not support object inheritance"

let delays_dot = refl_dot "Delays"

let structure_of_object structure_of_type context (fields : Metapp.Of.t list)
    : Ppxlib.core_type * Ppxlib.expression =
  let methods =
    List.map (structure_of_object_field structure_of_type context) fields in
  let structures, constructs = List.split methods in
  let types, descs = List.split structures in
  let construct, destruct = List.split constructs in
  let patterns, results = List.split construct in
  let construct = [Ppxlib.Ast_helper.Exp.case
    (ReflValuePat.list ~prefix:delays_dot patterns)
    (Ppxlib.Ast_helper.Exp.object_ (Ppxlib.Ast_helper.Cstr.mk [%pat? _] results))] in
  let destruct =
    [Ppxlib.Ast_helper.Exp.case (ReflValuePat.var "c")
       (ReflValueExp.list ~prefix:delays_dot destruct)] in
  [%type: [`Object of [%t type_sequence_of_list types]]],
  [%expr Refl.Object {
    methods = [%e ReflValueExp.object_methods_of_list descs];
    construct = [%e Ppxlib.Ast_helper.Exp.function_ construct];
    destruct = [%e Ppxlib.Ast_helper.Exp.function_ destruct];
  }]

let make_variables variable_count variables selector e =
  let list = List.init variable_count begin fun i ->
    Constraints.Variables.make_transfer variables selector i |>
    make_transfer [%type: [`Present]] [%type: [`Absent]] compose_type
  end in
  append_type_sequence_of_list list e

let make_presences variable_count variables =
  iterate_i [%expr Refl.Presences]
    (fun i acc ->
      Constraints.Variables.make_transfer variables Direct i |>
      make_transfer [%expr Refl.AddPresent [%e acc]]
        [%expr Refl.AddAbsent [%e acc]] compose_expr)
    variable_count

let constructor_of_attr_name attr_name =
  Printf.sprintf "Attribute_%s" attr_name

let rec lid_of_rev_path rev_path name : Longident.t =
  match rev_path with
  | [] -> Lident name
  | head :: tail ->
      Ldot (lid_of_rev_path tail head, name)

let lid_of_attr_name attr_name =
  match List.rev (String.split_on_char '.' attr_name) with
  | [] -> assert false
  | head :: tail ->
      lid_of_rev_path (List.map String.capitalize_ascii tail)
        (constructor_of_attr_name head)

let make_arity_types arity =
  type_sequence_of_list (List.init arity
    (fun i -> type_constr_of_string (type_arg i)))

let make_attributes context ty attributes : Ppxlib.expression =
  let cases =
    attributes |> List.map begin fun (attribute : Ppxlib.attribute) ->
      let name = lid_of_attr_name (Metapp.Attr.name attribute).txt in
      let name : Longident.t =
        match name with
        | Ldot (Lident "Ocaml", attr) ->
            Ldot (Ldot (Lident "Refl", "Ocaml_attributes"), attr)
        | _ -> name in
      let expr = Metapp.Exp.of_payload (Metapp.Attr.payload attribute) in
      Ppxlib.Ast_helper.Exp.case (Metapp.Pat.construct name [])
        [%expr Some [%e expr]]
    end in
  let cases =
    cases @ [Ppxlib.Ast_helper.Exp.case (Ppxlib.Ast_helper.Pat.any ()) [%expr None ]] in
  let accu = ref StringSet.empty in
  let ty =
    subst_free_variables (instantiate_with_free accu context.vars.map) ty in
  let arity_types = make_arity_types (StringIndexer.count context.vars) in
  let forall_types =
    List.map Metapp.mkloc
      ("__attribute" :: StringSet.elements !accu) in
  [%expr
     { Refl.typed = [%e List.fold_right Metapp.Exp.newtype forall_types
          (Ppxlib.Ast_helper.Exp.constraint_
             (Ppxlib.Ast_helper.Exp.function_ cases)
             [%type:
                ([%t ty], [%t arity_types], __attribute)
                  Refl.typed_attribute_kind ->
                __attribute option])] }]

let transform_attr context structure desc (ty : Ppxlib.core_type) =
  match ty.ptyp_attributes with
  | [] -> structure, desc
  | attr ->
      let attributes = make_attributes context ty attr in
      [%type: [`Attributes of [%t structure]]],
      [%expr Refl.Attributes {
          attributes = [%e attributes];
          desc = [%e desc];
        }]

let rec structure_of_type context (ty : Ppxlib.core_type)
    : Ppxlib.core_type * Ppxlib.expression =
  Ppxlib.Ast_helper.with_default_loc ty.ptyp_loc @@ fun () ->
  let transform ty =
    match ty with
    | [%type: _] ->
        let var = free_variable context in
        context.constraints |> Metapp.mutate begin
          Constraints.add_variable var.index
            (context.origin, context.selector)
        end;
        Ppxlib.Ast_helper.Typ.var var.name, ident_of_str (Metapp.mkloc var.name)
    | { ptyp_desc = Ptyp_var s; _ } ->
        begin match StringIndexer.find_opt s context.vars with
        | Some i ->
            context.constraints |> Metapp.mutate begin fun c -> c |>
              Constraints.add_direct_kind "Variable" |>
              Constraints.add_variable i (context.origin, context.selector)
            end;
            [%type: [`Variable of [%t peano_type_of_int i]]],
            [%expr Refl.Variable [%e ReflValueExp.variable_of_int i]]
        | None ->
            let var = name_free_variable context s in
            context.constraints |> Metapp.mutate begin
              Constraints.add_variable var.index
                (context.origin, context.selector)
            end;
            Ppxlib.Ast_helper.Typ.var var.name,
            ident_of_str (Metapp.mkloc var.name)
        end
    | { ptyp_desc = Ptyp_arrow (label, parameter, result); _} ->
        context.constraints |> Metapp.mutate
          (Constraints.add_direct_kind "Arrow");
        structure_of_arrow structure_of_type context label parameter
          result
    | { ptyp_desc = Ptyp_tuple types; _ } ->
        context.constraints |> Metapp.mutate
          (Constraints.add_direct_kind "Tuple");
        structure_of_tuple structure_of_type context types
    | { ptyp_desc = Ptyp_constr (constr, args); _ } ->
        begin match
          find_rec_type context constr.txt,
          Metapp.Attr.find "nobuiltin" ty.ptyp_attributes
        with
        | None, None ->
            structure_of_builtins_or_constr structure_of_type context ty
              constr.txt args
        | rec_type, _ ->
            structure_of_constr structure_of_type context constr.txt args
              ?rec_type
        end
    | { ptyp_desc = Ptyp_variant (fields, _, _); _ } ->
        context.constraints |> Metapp.mutate
          (Constraints.add_direct_kind "Variant");
        structure_of_variant structure_of_type context fields
    | { ptyp_desc = Ptyp_object (methods, closed_flag); _ } ->
        if closed_flag = Open then
          Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc
            "Open object types are not supported by ppx_refl";
        context.constraints |> Metapp.mutate
          (Constraints.add_direct_kind "Object");
        structure_of_object structure_of_type context methods
    | { ptyp_desc = Ptyp_alias (ty, name); _ } ->
        let var = name_free_variable context name in
        var.bound <- true;
        let structure, desc = structure_of_type context ty in
        Ppxlib.Ast_helper.Typ.alias structure var.name,
        Ppxlib.Ast_helper.Exp.let_ Recursive [Ppxlib.Ast_helper.Vb.mk
          (Metapp.Pat.var var.name) desc]
          (Metapp.Exp.var var.name)
    | { ptyp_desc = Ptyp_poly (vars, ty); _ } ->
        let context = { context with vars = context.vars |>
          StringIndexer.union (StringIndexer.of_list
            (vars |> List.map (fun var -> Some (Metapp.Typ.poly_name var))))} in
        structure_of_type context ty
    | _ ->
        Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc "Unsupported type" in
  match Metapp.Attr.chop "opaque" ty.ptyp_attributes with
  | Some (_, attributes) ->
      let ty = { ty with ptyp_attributes = attributes } in
      let ty = subst_free_variables (subst_type_vars context.vars.map) ty in
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Opaque");
      let eq_index = !(context.eqs_counter) in
      context.eqs_counter := succ eq_index;
      context.rev_eqs := ty :: !(context.rev_eqs);
      let structure =
        [%type: [`Opaque of [%t peano_type_of_int eq_index]]] in
      let desc =
        [%expr Refl.Opaque
          [%e ReflValueExp.selection_of_int (succ eq_index)]] in
      transform_attr context structure desc ty
  | _ ->
      match Metapp.Attr.chop "mapopaque" ty.ptyp_attributes with
      | None ->
          let structure, desc = transform ty in
          transform_attr context structure desc ty
      | Some (_, attributes) ->
          context.constraints |>
            Metapp.mutate (Constraints.add_direct_kind "MapOpaque");
          let kinds = fst !(context.constraints) in
          let ty = { ty with ptyp_attributes = attributes } in
          let structure, desc = transform ty in
          let structure, desc = transform_attr context structure desc ty in
          context.constraints := (kinds, snd !(context.constraints));
          let variable_count = StringIndexer.count context.vars in
          let variables = snd !(context.constraints) in
          let direct_type =
            make_variables variable_count variables Direct [%type: unit] in
          [%type: [`MapOpaque of [%t structure] * [%t direct_type]]],
          [%expr Refl.MapOpaque { desc = [%e desc] }]

let fold_free_variables
    (f : Location.t -> string option -> 'acc -> 'acc)
    (ty : Ppxlib.core_type) (acc : 'acc) : 'acc =
  let fold = object
    inherit ['acc] Ppxlib.Ast_traverse.fold as super

    method! core_type ty acc =
      match var_of_core_type_opt ty with
      | None -> super#core_type ty acc
      | Some var -> f ty.ptyp_loc var acc
  end in
  fold#core_type ty acc

let fold_map_free_variables
    (f : Location.t -> string option -> 'acc -> Ppxlib.core_type * 'acc)
    (ty : Ppxlib.core_type)  (acc : 'acc) : Ppxlib.core_type * 'acc =
  let fold_map = object
    inherit ['acc] Ppxlib.Ast_traverse.fold_map as super

    method! core_type ty acc =
      match var_of_core_type_opt ty with
      | None -> super#core_type ty acc
      | Some var -> f ty.ptyp_loc var acc
  end in
  fold_map#core_type ty acc

let extract_gadt_equalities context
    (constructor : Ppxlib.constructor_declaration) =
  match constructor.pcd_res with
  | None -> [], context
  | Some ty ->
      let args =
        match ty with
        | { ptyp_desc = Ptyp_constr ({ txt = Lident name; _ }, args); _ }
          when Some name = context.name -> args
        | _ ->
            Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc
              "Type constructor '%s' expected" (Option.get context.name) in
      let arg_count = List.length args in
      let arity = StringIndexer.count context.vars in
      if arg_count <> arity then
        Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc
"Type constructor '%s' has %d parameters but %d arguments given"
          (Option.get context.name) arity arg_count;
      let add_eq (eqs, vars) arg =
        match var_of_core_type_opt arg with
        | Some None ->
            let (_, vars) = StringIndexer.fresh vars in
            (eqs, vars)
        | Some (Some var) when not (StringIndexer.mem var vars) ->
            let (_, vars) = StringIndexer.force_add var vars in
            (eqs, vars)
        | _ ->
            let (index, vars) = StringIndexer.fresh vars in
            ((index, arg) :: eqs, vars) in
      let eqs, vars =
        List.fold_left add_eq ([], StringIndexer.empty) args in
      let eqs =
        eqs |> List.map begin fun (index, ty) ->
          let a = Ppxlib.Ast_helper.Typ.var (type_arg index) in
          let b = subst_free_variables (subst_type_vars vars.map) ty in
          [%type: ([%t a], [%t b]) Refl.eq]
        end in
      if eqs <> [] then
        context.constraints |>
          Metapp.mutate (Constraints.add_direct_kind "GADT");
      eqs, { context with vars }

let args_of_constructor (constructor : Ppxlib.constructor_declaration)
    : Ppxlib.core_type list =
  match constructor.pcd_args with
  | Pcstr_tuple items -> items
  | Pcstr_record labels ->
      List.map (fun (label : Ppxlib.label_declaration) -> label.pld_type)
        labels

let variables_type name arity sign =
  type_sequence_of_list (List.init arity (fun i ->
    type_constr_of_string (sign name i)
      ~args:[[%type: [`Present]]; [%type: [`Absent]]]))

type variables_structure = {
    arity_types : Ppxlib.core_type;
    count_length : Metapp.value;
    count_append : Metapp.value;
    variables : Ppxlib.expression;
    positives : Ppxlib.core_type;
    negatives : Ppxlib.core_type;
    directs : Ppxlib.core_type;
    positive : Ppxlib.core_type;
    negative : Ppxlib.core_type;
    direct : Ppxlib.core_type;
  }

let make_variables_structure context variable_count variables =
  let presences = make_presences variable_count variables in
  let count_length = ReflValueVal.length_of_int variable_count in
  let count_append = ReflValueVal.append_of_int variable_count in
  let initial_arity = StringIndexer.count context.vars in
  let arity_types = make_arity_types initial_arity in
  { arity_types;
    count_length;
    count_append;
    variables = [%expr {
      presences = [%e presences];
      positive_count = [%e count_length.exp];
      positive = [%e count_append.exp];
      negative_count = [%e count_length.exp];
      negative = [%e count_append.exp];
      direct_count = [%e count_length.exp];
      direct = [%e count_append.exp];
    }];
    positives = make_variables variable_count variables Right [%type: unit];
    negatives = make_variables variable_count variables Left [%type: unit];
    directs = make_variables variable_count variables Direct [%type: unit];
    positive =
      make_variables variable_count variables Right
        (variables_type (Option.get context.name) initial_arity
          Constraints.Variables.positive_name);
    negative =
      make_variables variable_count variables Left
        (variables_type (Option.get context.name) initial_arity
          Constraints.Variables.negative_name);
    direct =
      make_variables variable_count variables Direct
        (variables_type (Option.get context.name) initial_arity
          Constraints.Variables.direct_name);
  }

let is_singleton list =
  match list with
  | [_] -> true
  | _ -> false

let empty_type_annotation =
  Ppxlib.Asttypes.NoVariance, Ppxlib.Asttypes.NoInjectivity

let structure_of_label_declaration context prefix single_label
    (label : Ppxlib.label_declaration) item =
  match label.pld_type with
  | { ptyp_desc = Ptyp_poly (vars, field_type); _ } ->
      context.constraints |>
        Metapp.mutate (Constraints.add_direct_kind "Poly");
      let free_variables =
        StringIndexer.of_list
          (List.map (fun v -> Some (Metapp.Typ.poly_name v)) vars) in
      let vars = context.vars |> StringIndexer.union free_variables in
      let context' =
        { context with vars; constraints = ref Constraints.bottom } in
      let field_structure, field_desc =
        structure_of_type context' field_type in
      let variables = snd !(context'.constraints) in
      context.constraints :=
        Constraints.union !(context.constraints) !(context'.constraints);
      let count = StringIndexer.count free_variables in
      let count_type = peano_type_of_int count in
      let { arity_types; count_length; count_append; variables; positives;
            negatives; directs; positive; negative; direct } =
        make_variables_structure context count variables in
      let structure =
        [%type: [`Poly of [%t field_structure] * [%t count_type] *
          [%t positives] * [%t negatives] * [%t directs]]] in
      let type_args = List.map type_constr_of_string context.type_args in
      let kinds = type_constr_of_string context.type_names.kinds in
      let rec_group = type_constr_of_string context.type_names.rec_group in
      let gadt =
        type_constr_of_string context.type_names.gadt ~args:type_args in
      let internal_name, internal_label, type_declarations =
        if single_label then
          Option.get context.name, label.pld_name, []
        else
          let internal_name =
            Printf.sprintf "%s__%s" prefix label.pld_name.txt in
          let internal_name_str = Metapp.mkloc internal_name in
          let type_declaration =
            Ppxlib.Ast_helper.Type.mk internal_name_str
              ~params:(List.map (fun x -> x, empty_type_annotation)
                 context.original_vars)
              ~kind:(Ptype_record [Ppxlib.Ast_helper.Type.field
                internal_name_str label.pld_type]) in
          internal_name, internal_name_str, [type_declaration] in
      let destructed = ReflValueVal.record [Lident internal_label.txt, item] in
      let internal_type =
        type_constr_of_string internal_name ~args:type_args in
      let desc =
        [%expr
          let substructure = [%e field_desc] in
          let forall_destruct : type forall subarity .
            ([%t count_type], forall) Refl.length ->
            (forall, [%t arity_types], subarity) Refl.append ->
            ([%t internal_type], [%t field_structure], subarity,
              [%t rec_group], [> [%t kinds]], [%t positive], [%t negative],
              [%t direct], [%t gadt]) Refl.forall_destruct_result =
          fun [%p count_length.pat]
              [%p count_append.pat] ->
            Refl.ForallDestruct {
              desc = substructure;
              destruct = fun
                [%p Ppxlib.Ast_helper.Pat.record
                  [Metapp.lid_of_str internal_label,
                    Ppxlib.Ast_helper.Pat.var internal_label] Closed] ->
                [%e Ppxlib.Ast_helper.Exp.ident
                   (Metapp.lid_of_str internal_label)];
            } in
          Refl.Poly {
            label = [%e expr_of_string label.pld_name.txt];
            variables = [%e variables];
            destruct = { forall_destruct };
            construct = fun { forall_construct } ->
              [%e Ppxlib.Ast_helper.Exp.record [Metapp.lid_of_str internal_label,
                [%expr fun x -> forall_construct
                  [%e count_length.exp]
                  [%e count_append.exp] substructure x]]
                None]}] in
      (structure, desc), ((destructed, internal_type), type_declarations)
  | field_type ->
      let field_structure, field_desc =
        structure_of_type context field_type in
      let structure = [%type: [`Mono of [%t field_structure]]] in
      let desc =
        [%expr Refl.Mono {
          label = [%e expr_of_string label.pld_name.txt];
          desc = [%e field_desc];
          attributes =
            [%e make_attributes context field_type label.pld_attributes]; }] in
      (structure, desc), ((item, field_type), [])

let make_constructor_kind context
    (constructor : Ppxlib.constructor_declaration)
    (args : Ppxlib.core_type list) :
    Metapp.value list * Ppxlib.core_type * Ppxlib.core_type list *
    Ppxlib.expression * Metapp.value list *
    Ppxlib.type_declaration list =
  let items = List.mapi (fun i _ -> Metapp.Value.var (item i)) args in
  match constructor.pcd_args with
  | Pcstr_tuple _ ->
      let structures = List.map (structure_of_type context) args in
      let types, descs = List.split structures in
      let arg_types =
        args |> List.map
          (subst_free_variables (subst_type_vars context.vars.map)) in
      items,
      [%type: [`Tuple of [%t type_sequence_of_list types]]],
      arg_types,
      [%expr Refl.CTuple [%e ReflValueExp.tuple_of_list descs]],
      items, []
  | Pcstr_record labels ->
      let single_label = is_singleton labels in
      let prefix =
        Printf.sprintf "%s__%s" (Option.get context.name)
          constructor.pcd_name.txt in
      let structures =
        List.map2 (structure_of_label_declaration context prefix single_label)
          labels items in
      let structures, destructs = List.split structures in
      let types, descs = List.split structures in
      let destructs, type_declarations = List.split destructs in
      let destructs, arg_types = List.split destructs in
      let type_declarations = List.flatten type_declarations in
      let arg_types =
        arg_types |> List.map
          (subst_free_variables (subst_type_vars context.vars.map)) in
      items,
      [%type: [`Record of [%t type_sequence_of_list types]]],
      arg_types,
      [%expr Refl.CRecord [%e ReflValueExp.record_of_list descs]],
      destructs,
      type_declarations

let make_constructor_args (constructor : Ppxlib.constructor_declaration)
    items =
  match items with
  | [] -> None
  | _ :: _ ->
      let args =
        match constructor.pcd_args with
        | Pcstr_tuple _ -> Metapp.Value.tuple items
        | Pcstr_record labels ->
           let fields =
             List.map2 begin fun (label : Ppxlib.label_declaration) x ->
               Longident.Lident label.pld_name.txt, x
             end labels items in
           Metapp.Value.record fields in
      Some args

let tuple_of_types types =
  match types with
  | [] -> [%type: unit]
  | [ty] -> ty
  | _ -> Ppxlib.Ast_helper.Typ.tuple types

let rec fold_map_aux f list acc_list accu =
  match list with
  | [] -> (List.rev acc_list, accu)
  | head :: tail ->
      let (value, accu) = f head accu in
      fold_map_aux f tail (value :: acc_list) accu

let fold_map f list accu =
  fold_map_aux f list [] accu

let structure_of_exists single_constructor ctor_count i context
    (constructor : Ppxlib.constructor_declaration)
    (result : Ppxlib.core_type)
    : (((Ppxlib.core_type * Ppxlib.expression)
        * Ppxlib.core_type) *
      (Ppxlib.case * Ppxlib.case)) *
    (Ppxlib.type_declaration list * Ppxlib.type_extension list) =
  let result_args =
    match result with
    | { ptyp_desc = Ptyp_constr (_, args); _ } -> args
    | _ -> assert false in
  let add_arg (parameters, vars) arg =
    match var_of_core_type_opt arg with
    | Some None ->
        let (_, vars) = StringIndexer.fresh vars in
        (parameters, vars)
    | Some (Some var) ->
        begin match StringIndexer.find_opt var vars with
        | None ->
            let (_, vars) = StringIndexer.force_add var vars in
            (parameters, vars)
        | Some index' ->
            let (index, vars) = StringIndexer.fresh vars in
            ((index, arg) :: (index', arg) :: parameters, vars)
          end
    | _ ->
        let (index, vars) = StringIndexer.fresh vars in
        ((index, arg) :: parameters, vars) in
  let (parameters, vars) =
    List.fold_left add_arg ([], StringIndexer.empty) result_args in
  let check_free_variable _loc var indexer =
    let (var, indexer) =
      match var with
      | None ->
          let var =
            Printf.sprintf "free_var__%d" (StringIndexer.count indexer) in
          let (_, indexer) = StringIndexer.force_add var indexer in
          (var, indexer)
      | Some var ->
          if StringIndexer.mem var vars then
            (var, indexer)
          else
            let (_, indexer) = StringIndexer.add var indexer in
            (var, indexer) in
    (Ppxlib.Ast_helper.Typ.var var, indexer) in
  let args = args_of_constructor constructor in
  let (parameters, renamed_args), free_variables =
    let (parameters, indexer) =
      fold_map begin fun (index, arg) indexer ->
        let (arg, indexer) =
          fold_map_free_variables check_free_variable arg indexer in
        ((index, arg), indexer)
      end parameters StringIndexer.empty in
    let (renamed_args, indexer) =
      fold_map (fold_map_free_variables check_free_variable) args indexer in
    ((parameters, renamed_args), indexer) in
  let vars = vars |> StringIndexer.union free_variables in
  let branch_name =
    Printf.sprintf "%s_%s" (Option.get context.name) constructor.pcd_name.txt in
  let context' = { context with vars;
    constraints = ref Constraints.bottom;
    gadt_args = result_args; } in
  let items, structure, _types, kind, destructs, type_declarations =
    make_constructor_kind context' constructor renamed_args in
  let free_variable_count = StringIndexer.count free_variables in
  context.constraints :=
    Constraints.union !(context.constraints)
      (Constraints.offset_variables free_variable_count
         !(context'.constraints));
  let eq_index = !(context.eqs_counter) in
  context.eqs_counter := eq_index + 1;
  let constructor_args = make_constructor_args constructor items in
  let constructor_with_args =
    Metapp.Value.force_construct
      (Metapp.mkloc (Longident.Lident constructor.pcd_name.txt))
      constructor_args in
  let count = peano_type_of_int free_variable_count in
  let composed, value_type_name, type_declarations =
    if single_constructor then
      constructor_with_args,
      Option.get context.name,
      type_declarations
    else
      let branch_constructor = String.capitalize_ascii branch_name in
      let res =
        type_constr_of_string branch_name ~args:result_args in
      let kind =
        Ppxlib.Ptype_variant [Ppxlib.Ast_helper.Type.constructor
           (Metapp.mkloc branch_constructor)
           ~args:(Pcstr_tuple args) ~res] in
      Metapp.Value.construct (Lident branch_constructor) items,
      branch_name,
      Ppxlib.Ast_helper.Type.mk (Metapp.mkloc branch_name) ~kind
        ~params:(List.map (fun x -> x, empty_type_annotation)
          context.type_vars) :: type_declarations in
  let type_args = List.map type_constr_of_string context.type_args in
  let value_type =
    type_constr_of_string value_type_name ~args:type_args in
  let parameter_types =
    parameters |> List.map begin fun (index, _) ->
      type_constr_of_string (type_arg index)
    end in
  let parameter_type_tuple = tuple_of_types parameter_types in
  let decomposed = ReflValueVal.sequence_of_list destructs in
  let parameter_tuple =
    tuple_of_types (parameters |> List.map (fun (_index, parameter) ->
      subst_free_variables (subst_type_vars vars.map) parameter)) in
  let parameter_sequence =
    type_sequence_of_list
      (List.init free_variable_count
         (fun i -> Ppxlib.Ast_helper.Typ.var (type_arg i))) in
  let type_extensions, constraints_pattern =
    if parameters = [] then
      [], ReflValueVal.construct (refl_dot "NoConstraints") []
    else
      let constraints = Printf.sprintf "Constraints_%s" branch_name in
      let constraints_pattern =
        ReflValueVal.construct (Lident constraints) [] in
      [(Ppxlib.Ast_helper.Te.mk (Metapp.mkloc (refl_dot "gadt_constraints"))
          ~params:[[%type: _], empty_type_annotation; [%type: _], empty_type_annotation]
           [Ppxlib.Ast_helper.Te.constructor (Metapp.mkloc constraints)
              (Pext_decl (Pcstr_tuple [], Some
                [%type: ([%t parameter_tuple], [%t parameter_sequence])
                  Refl.gadt_constraints]))])], constraints_pattern in
  let parameter_type_vars =
    parameters |> List.map begin fun (index, _) ->
      Ppxlib.Ast_helper.Typ.var (type_arg index)
    end in
  let parameter_type_vars_tuple = tuple_of_types parameter_type_vars in
  context.rev_eqs := parameter_type_vars_tuple :: !(context.rev_eqs);
  let kinds = type_constr_of_string context.type_names.kinds in
  let rec_group = type_constr_of_string context.type_names.rec_group in
  let gadt =
    type_constr_of_string context.type_names.gadt ~args:type_args in
  let variables = snd !(context'.constraints) in
  context.exists :=
    Some begin
      let previous =
        match !(context.exists) with
        | Some previous -> previous
        | None -> Absent in
      iterate_i previous
        (fun i acc ->
          Constraints.Variables.make_transfer variables Direct i |>
          make_transfer Constraints.Transfer.Present acc compose_transfer)
        free_variable_count
    end;
  let presence_type =
    iterate_i [%type: [`Absent]]
      (fun i acc ->
        Constraints.Variables.make_transfer variables Direct i |>
        make_transfer [%type: [`Present]] acc compose_type)
      free_variable_count in
  let presence_expr =
    iterate_i [%expr Refl.Absent]
      (fun i acc ->
        Constraints.Variables.make_transfer variables Direct i |>
        make_transfer [%expr Refl.Present] acc compose_expr)
      free_variable_count in
  let { arity_types; count_length; count_append; variables; positives;
        negatives; directs; positive; negative; direct } =
    make_variables_structure context free_variable_count variables in
  let ty =
    [%type: [`Exists of [%t peano_type_of_int eq_index]
      * [%t peano_type_of_int free_variable_count]
      * [%t structure] * [%t presence_type] * [%t positives]
      * [%t negatives] * [%t directs]]] in
  let match_constraints expr =
    if parameters = [] then expr
    else
      [%expr match _constraints with
      | [%p constraints_pattern.pat] -> [%e expr]
      | _ -> assert false] in
  let desc =
    [%expr
       let kind = [%e kind] in
       let construct :
         type exists subarity .
         ([%t count], exists) Refl.length ->
         ([%t parameter_type_tuple], exists) Refl.gadt_constraints ->
         (exists, [%t arity_types], subarity) Refl.append ->
         ([%t value_type], [%t structure], subarity, [%t rec_group],
           [> [%t kinds]], [%t positive], [%t negative], [%t direct], [%t gadt])
             Refl.exists_construct =
       fun exists_count _constraints exists ->
         let [%p count_length.pat] = exists_count in
         let [%p count_append.pat] = exists in
         [%e match_constraints [%expr
           Refl.ExistsConstruct {
             kind;
             construct =
               [%e Ppxlib.Ast_helper.Exp.function_
                  [Ppxlib.Ast_helper.Exp.case decomposed.pat composed.exp]];}]] in
       let destruct =
         [%e List.fold_right
            (fun txt e -> Metapp.Exp.newtype (Metapp.mkloc txt) e)
            context.type_args [%expr (fun
              ([%p composed.pat] : [%t value_type]) :
              ([%t count], [%t parameter_type_tuple],
             [%t value_type], [%t structure], [%t arity_types], [%t rec_group],
             [> [%t kinds]], [%t positive], [%t negative], [%t direct],
               [%t gadt])
             Refl.exists_destruct ->
         Refl.ExistsDestruct {
           exists_count = [%e count_length.exp];
           exists = [%e count_append.exp];
           constraints = [%e constraints_pattern.exp];
           kind;
           values = [%e decomposed.exp] })]] in
       Refl.Exists {
         name = [%e expr_of_string constructor.pcd_name.txt];
         construct;
         destruct;
         selection =
           [%e ReflValueExp.selection_of_int (succ eq_index)];
         presence = [%e presence_expr];
         variables = [%e variables]; }] in
  context.constraints |>
    Metapp.mutate (Constraints.add_direct_kind "Exists");
  let choice = ReflValueVal.binary_choice_of_int i ctor_count composed in
  let signature = (type_declarations, type_extensions) in
  (((ty, desc), value_type),
    (Ppxlib.Ast_helper.Exp.case choice.pat constructor_with_args.exp,
      Ppxlib.Ast_helper.Exp.case constructor_with_args.pat choice.exp)), signature

let structure_of_constructor single_constructor context count i
    (constructor : Ppxlib.constructor_declaration)
    : (((Ppxlib.core_type * Ppxlib.expression)
        * Ppxlib.core_type) *
         (Ppxlib.case * Ppxlib.case))
    * (Ppxlib.type_declaration list * Ppxlib.type_extension list) =
  try
    let eqs, context = extract_gadt_equalities context constructor in
    let args = args_of_constructor constructor in
    let items, ty, types, kind, destructs, type_declarations =
      make_constructor_kind context constructor args in
    let base_eq_index = !(context.eqs_counter) in
    let eq_count = List.length eqs in
    context.eqs_counter := base_eq_index + eq_count;
    context.rev_eqs := List.rev_append eqs !(context.rev_eqs);
    let gadt_indexes = List.init eq_count (fun i -> i + base_eq_index) in
    let eq_refs =
      ReflValueExp.equalities_of_list
        (List.map ReflValueExp.selection_of_int (List.map succ gadt_indexes)) in
    let gadt =
      type_sequence_of_list (List.map peano_type_of_int gadt_indexes) in
    let ty = [%type: [`Constructor of [%t ty] * [%t gadt]]] in
    let attributes =
      match constructor.pcd_args with
      | Pcstr_record labels when
        List.exists (fun (label : Ppxlib.label_declaration) ->
          match label.pld_type with
          | { ptyp_desc = Ptyp_poly _; _ } -> true
          | _ -> false ) labels ->
          [%expr Refl.Tools.attributes_empty]
      | _ ->
          make_attributes context (type_sequence_of_list args)
            constructor.pcd_attributes in
    let desc =
      [%expr Refl.Constructor {
        name = [%e expr_of_string constructor.pcd_name.txt];
        kind = [%e kind];
        eqs = [%e eq_refs];
        attributes = [%e attributes];
      }] in
    let value_eqs =
      List.init eq_count
        (fun _ -> Metapp.Value.construct (refl_dot "Eq") []) in
    let sequence =
      Metapp.Value.tuple
        [ReflValueVal.sequence_of_list destructs;
          ReflValueVal.sequence_of_list value_eqs] in
    let choice = ReflValueVal.binary_choice_of_int i count sequence in
    let args = make_constructor_args constructor items in
    let construct =
      Metapp.Value.force_construct
        (Metapp.mkloc (Longident.Lident constructor.pcd_name.txt)) args in
    let choice_ty =
      [%type: [%t type_sequence_of_list types]
         * [%t type_sequence_of_list eqs]] in
    (((ty, desc), choice_ty),
      (Ppxlib.Ast_helper.Exp.case choice.pat construct.exp,
        Ppxlib.Ast_helper.Exp.case construct.pat choice.exp)), (type_declarations, [])
  with (Exists (loc, name)) ->
    match constructor.pcd_res with
    | Some ty ->
        structure_of_exists single_constructor count i context constructor ty
    | None ->
        match name with
        | None ->
            Location.raise_errorf ~loc
              "Free variable types are not allowed outside GADT constructors"
        | Some name ->
            Location.raise_errorf ~loc
              "The type variable '%s is unbound in this type declaration." name

let temp_binding_count = ref 0

let structure_of_constr context
    (constructors : Ppxlib.constructor_declaration list)
    : (Ppxlib.core_type * Ppxlib.expression) *
      (Ppxlib.type_declaration list * Ppxlib.type_extension list * Ppxlib.structure) =
  let single_constructor = is_singleton constructors in
  let count = List.length constructors in
  let cases =
    List.mapi (structure_of_constructor single_constructor context count)
      constructors in
  let cases, signature = List.split cases in
  let cases, accessors = List.split cases in
  let structures, choices = List.split cases in
  let types, descs = List.split structures in
  let construct, destruct = List.split accessors in
  let construct = construct @ irrefutable () in
  let choice_ty =
    [%type: [%t binary_type_of_list choices] Refl.binary_choice] in
  let make_fun_type left right cases =
    let left = subst_free_variables instantiate left in
    let right = subst_free_variables instantiate right in
    let arrow_ty = [%type: [%t left] -> [%t right]] in
    [%expr ([%e Ppxlib.Ast_helper.Exp.function_ cases] : [%t arrow_ty])] in
  let bindings, descs =
    if context.type_vars = [] then
    List.fold_left_map (fun bindings ((cstr : Ppxlib.constructor_declaration), desc) ->
      if cstr.pcd_args = Pcstr_tuple [] && cstr.pcd_res = None then
        let temp_binding_index = !temp_binding_count in
        temp_binding_count := succ temp_binding_index;
        let construct_name = Printf.sprintf "constructor%d" temp_binding_index in
        [%stri let [%p Metapp.Pat.var construct_name] = [%e desc]
            (*assert false
           let module M = struct let v = [%e desc] end in
           let module T = struct module type S = module type of M end in
           let module (N : T.S) = struct let v = assert false end in
           let (m : (module T.S)) = if Random.int 2 < 1 then (module M) else (module N) in
           let module M' = (val m) in
           M'.v*)] :: bindings,
        [%expr Metapp.Exp.var construct_name]
      else
        bindings, desc)
      [] (List.combine constructors descs)
    else
      [], descs in
  context.constraints |> Metapp.mutate
    (Constraints.add_direct_kind "Constr");
  let expr =
    [%expr Refl.Constr {
      constructors = assert false (* [%e ReflValueExp.binary_choices_of_list descs] *);
      construct = [%e make_fun_type choice_ty context.type_expr construct];
      destruct = [%e make_fun_type context.type_expr choice_ty destruct];
    }] in
  let type_declarations, type_extensions = List.split signature in
  let type_declarations = List.flatten type_declarations in
  let type_extensions = List.flatten type_extensions in
  ([%type: [`Constr of [%t binary_type_of_list types]]], expr),
  (type_declarations, type_extensions, bindings)

let structure_of_record context (labels : Ppxlib.label_declaration list)
    : (Ppxlib.core_type * Ppxlib.expression) *
    (Ppxlib.type_declaration list * Ppxlib.type_extension list * 'a list) =
  let items =
    List.init (List.length labels) (fun i -> ReflValueVal.var (item i)) in
  context.constraints |> Metapp.mutate
    (Constraints.add_direct_kind "Record");
  let single_label = is_singleton labels in
  let structures =
    List.map2 (structure_of_label_declaration context (Option.get context.name)
      single_label) labels items in
  let structures, destructs = List.split structures in
  let types, descs = List.split structures in
  let destructs, type_declarations = List.split destructs in
  let type_declarations = List.flatten type_declarations in
  let destructs, _ = List.split destructs in
  let sequence = ReflValueVal.sequence_of_list destructs in
  let record =
    ReflValueVal.record
      (List.map2 (fun (label : Ppxlib.label_declaration) item ->
        (Longident.Lident label.pld_name.txt, item))
        labels items) in
  let expr =
    [%expr Refl.Record {
       structure = [%e ReflValueExp.record_of_list descs];
       construct = [%e Ppxlib.Ast_helper.Exp.function_
         [Ppxlib.Ast_helper.Exp.case sequence.pat record.exp]];
       destruct = [%e Ppxlib.Ast_helper.Exp.function_
         [Ppxlib.Ast_helper.Exp.case record.pat sequence.exp]];
     }] in
  ([%type: [`Record of [%t type_sequence_of_list types]]], expr),
  (type_declarations, [], [])

let structure_of_type_declaration context (td : Ppxlib.type_declaration)
    : (Ppxlib.core_type * Ppxlib.expression) *
    (Ppxlib.type_declaration list * Ppxlib.type_extension list * Ppxlib.structure_item list) =
  Ppxlib.Ast_helper.with_default_loc td.ptype_loc @@ fun () ->
  let (structure, unwrapped_desc), sides =
    match td.ptype_kind with
    | Ptype_variant constructors ->
        structure_of_constr context constructors
    | Ptype_record labels ->
        structure_of_record context labels
    | Ptype_abstract ->
        begin match td.ptype_manifest with
        | None ->
            Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc
              "refl cannot be derived for fully abstract types"
        | Some ty -> (structure_of_type context ty), ([], [], [])
        end
    | Ptype_open ->
        Location.raise_errorf ~loc:!Ppxlib.Ast_helper.default_loc
          "refl cannot be derived for open types" in
  let structure = [%type: [`Name of [%t structure]]] in
  let unwrapped_desc = [%expr Refl.Name {
    refl =
      [%e Metapp.Exp.construct (Lident (type_refl_ctor td.ptype_name.txt)) []];
    name = [%e Metapp.Exp.of_string td.ptype_name.txt];
    desc = [%e unwrapped_desc]; }] in
  (structure, unwrapped_desc), sides

type type_structure = {
    type_info : type_info;
    context : context;
    arity_type : Ppxlib.core_type;
    structure : Ppxlib.core_type;
    unwrapped_desc : Ppxlib.expression;
    constraints : Constraints.t;
    rec_type_refs : IntSet.t;
  }

let subgadt_mapper context type_extensions =
  let type_extension_count = ref 0 in
  let mapper = object
    inherit Ppxlib.Ast_traverse.map as super

    method! core_type ty =
      match super#core_type ty with
      | [%type: [`SubGADT of [%t? ty']]] ->
          if context.name = None then
            ty'
          else
            ty
      | ty -> ty

    method! expression e =
      match super#expression e with
      | [%expr Refl.SubGADT ([%e? desc] : [%t? base] -> [%t? sub])] ->
          begin match context.name with
          | None -> desc
          | Some name ->
            let index = !type_extension_count in
            type_extension_count := succ index;
            let constructor_name = Printf.sprintf "%s__sub_%d"
              (String.capitalize_ascii name) index in
            let constructor =
              Metapp.Value.construct (Lident constructor_name) [] in
            type_extensions :=
              Ppxlib.Ast_helper.Te.mk (Metapp.mkloc (refl_dot "sub_gadt_ext"))
           ~params:[[%type: _], empty_type_annotation; [%type: _], empty_type_annotation]
           [Ppxlib.Ast_helper.Te.constructor (Metapp.mkloc constructor_name)
              (Pext_decl (Pcstr_tuple [], Some
                [%type: ([%t base], [%t sub])
                  Refl.sub_gadt_ext]))] ::
              !type_extensions;
            [%expr
               let sub_gadt_functional : type gadt sub_gadt0 sub_gadt1 .
                  (gadt, sub_gadt0) Refl.sub_gadt_ext ->
                  (gadt, sub_gadt1) Refl.sub_gadt_ext ->
                  (sub_gadt0, sub_gadt1) Refl.eq =
                fun sub sub' ->
                  match sub, sub' with
                  | [%p constructor.pat], [%p constructor.pat] -> Eq
                  | _ -> assert false in
               Refl.SubGADT {
              desc = [%e desc];
              sub_gadt = {
                Refl.sub_gadt_ext = [%e constructor.exp];
                sub_gadt_functional }}]
          end
      | e -> e
  end in
  mapper

let type_structure_of_type_info rec_types type_info =
  let { arity; td; _ } = type_info in
  Ppxlib.Ast_helper.with_default_loc td.ptype_loc @@ fun () ->
  let context = context_of_type_declaration td rec_types in
  let (structure, unwrapped_desc), (type_declarations, type_extensions, value_bindings) =
    structure_of_type_declaration context td in
  let arity_type = peano_type_of_int arity in
  let type_extensions = ref type_extensions in
  let mapper = subgadt_mapper context type_extensions in
  let unwrapped_desc = mapper#expression unwrapped_desc in
  let structure = mapper#core_type structure in
  let declarations = [
    Ppxlib.Ast_helper.Type.mk (Metapp.mkloc context.type_names.arity)
      ~manifest:arity_type;
    Ppxlib.Ast_helper.Type.mk (Metapp.mkloc context.type_names.structure)
      ~manifest:structure;
  ] in
  let arity_type = type_constr_of_string context.type_names.arity in
  let structure = type_constr_of_string context.type_names.structure in
  let constraints = !(context.constraints) in
  let constraints =
    match !(context.exists) with
    | None -> constraints
    | Some exists ->
        Constraints.add_exists_kind exists constraints in
  let type_extensions = !type_extensions in
  let type_extensions =
    Ppxlib.Ast_helper.Te.mk (Metapp.mkloc (refl_dot "refl"))
      ~params:[[%type: _], empty_type_annotation]
      [Ppxlib.Ast_helper.Te.constructor
        (Metapp.mkloc context.type_names.refl_ctor)
        (Pext_decl (Pcstr_tuple [], Some
          [%type: [%t context.type_expr] Refl.refl]))]
  :: type_extensions in
  ((declarations @ type_declarations), (type_extensions, value_bindings)),
  { type_info; context; arity_type; structure; unwrapped_desc; constraints;
    rec_type_refs = !(context.rec_type_refs) }

let types_of_transfers transfers =
  let present = [%type: 'present] in
  let unknown = [%type: 'unknown] in
  let params = [present, empty_type_annotation; unknown, empty_type_annotation] in
  transfers |> List.map begin fun (name, transfer) ->
    let manifest = transfer |> make_transfer present unknown compose_type in
    Ppxlib.Ast_helper.Type.mk ~params (Metapp.mkloc name) ~manifest
  end

let funs_of_transfers transfers =
  transfers |> List.map begin fun (name, transfer) ->
    let str = Metapp.mkloc name in
    Ppxlib.Ast_helper.Val.mk str
      [%type: 'present -> 'unknown ->
        [%t Ppxlib.Ast_helper.Typ.constr (Metapp.lid_of_str str)
          [[%type: 'present]; [%type: 'unknown]]]],
    Ppxlib.Ast_helper.Vb.mk (Ppxlib.Ast_helper.Pat.var str)
      [%expr fun refl__present refl__absent ->
        [%e transfer |> make_transfer [%expr refl__present] [%expr refl__absent]
          compose_expr]]
      ~attrs:[Metapp.Attr.mk (Metapp.mkloc "ocaml.warning")
        (PStr [%str "-27-32"])]
  end

let module_of_type_structure rec_group constraints i type_structure
    :
    ((Ppxlib.type_declaration list * Ppxlib.type_declaration list) *
       (Ppxlib.value_description * Ppxlib.value_binding) list) *
    (Ppxlib.signature_item * Ppxlib.value_binding) =
  let { type_info = { td; desc_name; arity; _ };
    structure; unwrapped_desc; context; _ } = type_structure in
  Ppxlib.Ast_helper.with_default_loc td.ptype_loc @@ fun () ->
  let types = type_sequence_of_list context.type_vars in
  let rec_group_type = type_constr_of_string context.type_names.rec_group in
  let rec_group_decl =
    let (declared, manifest) = !rec_group in
    if not declared then
      rec_group := (true, rec_group_type);
    Ppxlib.Ast_helper.Type.mk (Metapp.mkloc context.type_names.rec_group)
      ~manifest in
  let constraints = constraints i in
  let kinds = type_constr_of_string context.type_names.kinds in
  let kinds_decl =
    let manifest = Constraints.Kinds.to_type (fst constraints) in
    Ppxlib.Ast_helper.Type.mk (Metapp.mkloc context.type_names.kinds)
      ~manifest in
  let variable_transfers =
    Constraints.Variables.make_transfers td.ptype_name.txt arity
      (snd constraints) in
  let transfers_types = types_of_transfers variable_transfers in
  let transfers_funs = funs_of_transfers variable_transfers in
  let variable_types name _absent =
    variable_types (Lident td.ptype_name.txt) arity name
      (fun _i -> [%type: [`Absent]]) in
  let gadt =
    type_constr_of_string context.type_names.gadt ~args:context.type_vars in
  let gadt_decl =
    let params =
      context.type_vars |> List.map (fun ty -> (ty, empty_type_annotation)) in
    let manifest = type_sequence_of_list (List.rev !(context.rev_eqs)) in
    Ppxlib.Ast_helper.Type.mk (Metapp.mkloc context.type_names.gadt) ~manifest
      ~params in
  let desc_type =
    [%type:
      ([%t context.type_expr], [%t structure], [%t types],
        [%t rec_group_type], [> [%t kinds]],
        [%t variable_types Constraints.Variables.positive_name
          (fun i -> "absent_positive" ^ string_of_int i)],
        [%t variable_types Constraints.Variables.negative_name
          (fun i -> "absent_negative" ^ string_of_int i)],
        [%t variable_types Constraints.Variables.direct_name
          (fun i -> "absent_direct" ^ string_of_int i)],
        [%t gadt]) Refl.desc] in
  let desc_sig =
    Ppxlib.Ast_helper.Sig.value (Ppxlib.Ast_helper.Val.mk (Metapp.mkloc desc_name)
      desc_type) in
  let type_loc = List.map Metapp.mkloc context.type_args in
  let desc =
    List.fold_right Metapp.Exp.newtype type_loc unwrapped_desc in
  let desc_def =
    Ppxlib.Ast_helper.Vb.mk
      [%pat? ([%p Metapp.Pat.var desc_name] :
        [%t Metapp.Typ.poly type_loc desc_type])]
      desc
      ~attrs:[Metapp.Attr.mk (Metapp.mkloc "ocaml.warning")
        (PStr [%str "-32-34"])] in
  ((transfers_types, [rec_group_decl; kinds_decl; gadt_decl]), transfers_funs),
  (desc_sig, desc_def)

let rec_types_of_type_info (rec_flag : Ppxlib.Asttypes.rec_flag) type_infos =
  match rec_flag with
  | Nonrecursive -> None
  | Recursive ->
      let count = List.length type_infos in
      Some (make_index (fun { td; _ } -> Some td.ptype_name.txt)
        type_infos count)

type modules = {
    desc_sig : Ppxlib.signature;
    desc_def : Ppxlib.structure;
  }

let modules_of_type_declarations (rec_flag, tds) =
  let recursive = ref Ppxlib.Asttypes.Nonrecursive in
  let type_infos =
    tds |> List.map (type_info_of_type_declaration recursive) in
  let rec_types = rec_types_of_type_info rec_flag type_infos in
  let type_structures =
    List.map (type_structure_of_type_info rec_types) type_infos in
  let signature, type_structures =
    List.split type_structures in
  let indexed_type_structures = Array.of_list type_structures in
  let module F = Fix.Fix.ForType (Int) (Constraints) in
  let constraints = F.lfp begin fun i constraints ->
    let type_structure = indexed_type_structures.(i) in
    let union j cstr =
      Constraints.union (constraints j) cstr in
    IntSet.fold union type_structure.rec_type_refs
      (Constraints.union (constraints i) type_structure.constraints)
  end in
  let rec_group_type =
    binary_type_of_list (type_structures |> List.map begin
      fun (type_structure : type_structure) : Ppxlib.core_type ->
        [%type: [%t type_structure.arity_type] * [%t type_structure.structure]]
    end) in
(*
  let rec_group_expr =
    rec_group_of_list (type_structures |> List.map begin
      fun (type_structure : type_structure) ->
        exp [%expr [%e expression_of_value
             (length_of_int type_structure.type_info.arity)],
           [%e Ppxlib.Ast_helper.Exp.ident { loc; txt =
             Lident (type_structure.type_info.desc_name)}]]
    end) in
*)
  let type_declarations, type_extensions = List.split signature in
  let type_declarations = List.flatten type_declarations in
  let type_extensions, value_bindings = List.split type_extensions in
  let type_extensions = List.flatten type_extensions in
  let value_bindings = List.flatten value_bindings in
  let desc =
    List.mapi
      (module_of_type_structure (ref (false, rec_group_type)) constraints)
      type_structures in
  let decls, desc = List.split desc in
  let types, vals = List.split decls in
  let transfers, types = List.split types in
  let type_declarations =
    List.flatten transfers @ type_declarations @ List.flatten types in
  let desc_sig, desc_bindings = List.split desc in
(*
  let rec_group_name = (List.hd type_structures).context.type_names.rec_group in
  let desc_sig =
    Ppxlib.Ast_helper.Sig.value (Ppxlib.Ast_helper.Value.mk { loc; txt = rec_group_name }
      (Ppxlib.Ast_helper.Typ.constr { loc; txt = (refl_dot "rec_group") }
         [type_constr_of_string rec_group_name;
           type_constr_of_string rec_group_name])) :: desc_sig in
  let desc_bindings =
    Ppxlib.Ast_helper.Vb.mk (Ppxlib.Ast_helper.Pat.var { loc; txt = rec_group_name })
      (expression_of_value rec_group_expr) :: desc_bindings in
*)
  let val_desc, val_bindings = List.split (List.flatten vals) in
  let val_sig = List.map Ppxlib.Ast_helper.Sig.value val_desc in
  let desc_def =
    Ppxlib.Ast_helper.Str.type_ Recursive type_declarations ::
    List.map Ppxlib.Ast_helper.Str.type_extension type_extensions @
    value_bindings @
    [Ppxlib.Ast_helper.Str.value !recursive desc_bindings] in
  let desc_sig =
    Ppxlib.Ast_helper.Sig.type_ Recursive type_declarations ::
    List.map Ppxlib.Ast_helper.Sig.type_extension type_extensions @
    val_sig @ desc_sig in
  let desc_def =
    if val_bindings = [] then
      desc_def
    else
      Ppxlib.Ast_helper.Str.value Nonrecursive val_bindings :: desc_def in
  { desc_sig; desc_def  }

let make_str ~loc type_declarations : Ppxlib.structure =
  Ppxlib.Ast_helper.with_default_loc loc @@ fun () ->
  let { desc_def; _ } =
    modules_of_type_declarations type_declarations in
  let stop_doc = [%str (**/**)] in
  stop_doc @ desc_def @ stop_doc

(*
let str_type_decl =
  Ppxlib.Deriving.Generator.make_noarg make_str
*)

let make_sig ~loc type_declarations : Ppxlib.signature =
  let { desc_sig; _ } =
    modules_of_type_declarations type_declarations in
  let stop_doc = [%sig: (**/**)] in
  stop_doc @ desc_sig @ stop_doc

(*
let sig_type_decl = Ppxlib.Deriving.Generator.make_noarg make_sig
*)

let enumerate_free_variables (ty : Ppxlib.core_type)
    : StringSet.t * int =
  fold_free_variables begin fun _loc var (names, anonymous) ->
    match var with
    | None -> names, anonymous + 1
    | Some name -> StringSet.add name names, anonymous
  end ty (StringSet.empty, 0)

let extension ty : Ppxlib.expression =
  let names, anonymous = enumerate_free_variables ty in
  let arity = StringSet.cardinal names + anonymous in
  let context = make_context None [] (StringIndexer.of_fresh arity) in
  let _structure, expr = structure_of_type context ty in
  let mapper = subgadt_mapper context (ref []) in
  let expr = mapper#expression expr in
  let expr =
    match !(context.free_vars) with
    | [] -> expr
    | free_vars ->
        let bindings =
          List.rev free_vars |>
          List.filter (fun var -> not var.bound) |>
          List.mapi begin fun i (var : free_variable) ->
            Ppxlib.Ast_helper.Vb.mk (Metapp.Pat.var var.name)
              [%expr Refl.Variable [%e ReflValueExp.variable_of_int i]]
          end in
        Ppxlib.Ast_helper.Exp.let_ Nonrecursive bindings expr in
  expr

let sig_type_decl =
  Ppxlib.Deriving.Generator.make Ppxlib.Deriving.Args.empty
    (fun ~loc ~path:_ -> make_sig ~loc)

let str_type_decl =
  Ppxlib.Deriving.Generator.make Ppxlib.Deriving.Args.empty
    (fun ~loc ~path:_ -> make_str ~loc)

let () =
  Ppxlib.Deriving.add "refl"
    ~sig_type_decl
    ~str_type_decl
    ~extension:(fun ~loc:_ ~path:_ -> extension) |>
  Ppxlib.Deriving.ignore

(*
  let var_list = ref [] in
  let var_counter = ref 0 in
  let fresh_var () =
    let index = !var_counter in
    let var_name = Printf.sprintf "free%d" index in
    var_list := var_name :: !var_list;
    Ppxlib.Ast_helper.Typ.var var_name in
  let table = StringHashtbl.create 17 in
  let f _ var =
    match var with
    | None -> fresh_var ()
    | Some name ->
        try StringHashtbl.find table name
        with Not_found ->
          let result = fresh_var () in
          StringHashtbl.add table name result;
          result in
  let target_type = subst_free_variables f ty in
  let var_list = !var_list in
  let arity = type_sequence_of_list (List.map Ppxlib.Ast_helper.Typ.var var_list) in
  let ty = [%type: (
    [%t target_type], _, [%t arity], _, _, _, _, _) Refl.desc] in
  let ty =
    if var_list = [] then
      ty
    else
      Ppxlib.Ast_helper.Typ.poly (List.map (fun txt -> { loc; txt }) var_list) ty in
  [%expr let result : [%t ty] = [%e expr] in result]
*)
(*
let deriver =
  Ppxlib.Deriving.add "refl" ~str_type_decl ~sig_type_decl ~extension
*)
