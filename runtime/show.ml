open Desc

open Tools

module Printer = struct
  type 'a t = Format.formatter -> 'a -> unit
end

module PrinterSequence = Sequence (Printer)

type ('a, 'arity, 'b) typed_attribute_kind +=
  | Attribute_printer : ('a, 'arity, 'a Printer.t) typed_attribute_kind
  | Attribute_polyprinter :
      ('a, 'arity, 'arity PrinterSequence.t -> 'a Printer.t)
      typed_attribute_kind

module Printers = Vector (Printer)

type 'kinds value =
  | Value : {
      desc :
        ('a, 'structure, 'arity, 'rec_arity, 'kinds, 'positive, 'negative,
          'direct, 'gadt) desc;
      value : 'a;
      printers : ('arity, 'direct) Printers.t;
    } ->
      'kinds value

let rec pp :
  type a structure arity rec_arity positive negative direct gadt .
  (a, structure, arity, rec_arity, 'kinds, positive, negative, direct, gadt)
    desc ->
      (arity, direct) Printers.t -> a Printer.t =
fun desc printers fmt x ->
  let pp_tuple printers tuple =
    let pp_tuple_item (Tuple.Fold { desc; value; _ })
        comma =
      if comma then
        begin
          Format.pp_print_string fmt ",";
          Format.pp_print_space fmt ();
        end;
      Format.pp_open_box fmt 0;
      pp desc printers fmt value;
      Format.pp_close_box fmt ();
      true in
    Format.pp_open_box fmt 1;
    Format.pp_print_string fmt "(";
    ignore (Tuple.fold pp_tuple_item tuple false);
    Format.pp_print_string fmt ")";
    Format.pp_close_box fmt () in

  let pp_record printers record =
    let pp_record_field (Record.Fold { field; value; _ }) comma =
      if comma then
        begin
          Format.pp_print_string fmt ";";
          Format.pp_print_space fmt ();
        end;
      Format.pp_open_box fmt 0;
      let pp_field label desc printers value =
        Format.pp_print_string fmt label;
        Format.pp_print_string fmt " =";
        Format.pp_print_space fmt ();
        pp desc printers fmt value in
      begin match field with
      | Poly { label; destruct; variables; _ } ->
          let MakeAppend subarity = make_append variables.direct_count in
          let printers =
            printers |>
            Printers.append None
              variables.presences variables.direct_count variables.direct
              variables.direct_count subarity in
          let ForallDestruct { desc; destruct } =
            destruct.forall_destruct variables.direct_count subarity in
          pp_field label desc printers (destruct value)
      | Mono { label; desc; _ } -> pp_field label desc printers value;
      end;
      Format.pp_close_box fmt ();
      true in
    Format.pp_open_box fmt 2;
    Format.pp_print_string fmt "{ ";
    ignore (Record.fold pp_record_field record false);
    Format.pp_print_space fmt ();
    Format.pp_print_string fmt "}";
    Format.pp_close_box fmt () in

  let rec to_list_aux :
    type a structure arity rec_arity positive negative direct gadt .
    (a, structure, arity, rec_arity, 'kinds, positive, negative, direct,
      gadt) desc ->
    a ->
    (arity, direct) Printers.t ->
    'kinds value list ->
    'kinds value list option =
  fun desc value printers acc ->
    match desc with
    | Constr { constructors; destruct; _ } ->
        let Destruct destruct =
          Constructor.destruct constructors (destruct value) in
        let printers =
          match destruct.link with
          | Exists { exists_count; exists; variables; _ } ->
              printers |>
              Printers.append
                (Some { item = fun fmt _ ->
                  Format.pp_print_string fmt "<poly>" })
                variables.presences variables.direct_count variables.direct
                exists_count exists
          | Constructor -> printers in
        begin match destruct.name, destruct.kind, destruct.values with
        | "[]", Tuple { structure = []; _ }, _ -> Some (List.rev acc)
        | "::",
          Tuple { structure = [desc; tail_desc]; _ }, (value, (tail, ())) ->
            to_list_aux tail_desc tail printers
              (Value { desc; value; printers } :: acc)
        | _ -> None
        end
    | Apply { arguments; desc; transfer } ->
        let printers =
          Printers.make { f = pp } arguments transfer printers in
        to_list_aux desc value printers acc
    | Rec { desc; _ } ->
        to_list_aux desc value printers acc
    | RecArity { desc } ->
        to_list_aux desc value printers acc
    | SelectGADT { desc; _ } ->
        to_list_aux desc value printers acc
    | SubGADT { desc; _ } ->
        to_list_aux desc value printers acc
    | Name { desc; _ } ->
        to_list_aux desc value printers acc
    | _ ->
        None in

  let to_list desc value printers =
    to_list_aux desc value printers [] in

  match desc with
  | Variable index ->
      Printers.get index printers fmt x
  | Builtin Bool -> Format.pp_print_bool fmt x
  | Builtin Bytes ->
      Format.pp_print_string fmt "\"";
      Format.pp_print_string fmt (String.escaped (Bytes.to_string x));
      Format.pp_print_string fmt "\""
  | Builtin Char ->
      Format.pp_print_string fmt "'";
      Format.pp_print_string fmt (String.escaped (String.make 1 x));
      Format.pp_print_string fmt "'"
  | Builtin Float ->
      Format.pp_print_float fmt x
  | Builtin Int ->
      Format.pp_print_int fmt x
  | Builtin Int32 ->
      Format.pp_print_string fmt (Int32.to_string x);
      Format.pp_print_string fmt "l"
  | Builtin Int64 ->
      Format.pp_print_string fmt (Int64.to_string x);
      Format.pp_print_string fmt "L"
  | Builtin Nativeint ->
      Format.pp_print_string fmt (Nativeint.to_string x);
      Format.pp_print_string fmt "n"
  | Builtin String ->
      Format.pp_print_string fmt "\"";
      Format.pp_print_string fmt (String.escaped x);
      Format.pp_print_string fmt "\""
  | Arrow _ | LabelledArrow _ ->
      Format.pp_print_string fmt "<fun>"
  | Array desc ->
      Format.pp_open_box fmt 2;
      Format.pp_print_string fmt "[|";
      let pp_value comma value =
        if comma then
          begin
            Format.pp_print_string fmt ";";
            Format.pp_print_space fmt ();
          end;
        pp desc printers fmt value;
        true in
      ignore (Array.fold_left pp_value false x);
      Format.pp_print_string fmt "|]";
      Format.pp_close_box fmt ()
  | Constr { constructors; destruct; _ } ->
      let Destruct destruct =
        Constructor.destruct constructors (destruct x) in
      let printers' =
        match destruct.link with
        | Exists { exists_count; exists; variables; _ } ->
            printers |>
            Printers.append
              (Some { item = fun fmt _ -> Format.pp_print_string fmt "<poly>" })
              variables.presences variables.direct_count variables.direct
              exists_count exists
        | Constructor -> printers in
      begin match destruct.name, destruct.kind with
      | "::", Tuple { structure = [head_desc; tail_desc]; _ } ->
          begin match to_list desc x printers with
          | Some list ->
              Format.pp_open_box fmt 1;
              Format.pp_print_string fmt "[";
              let pp_value comma (Value { desc; value; printers }) =
                if comma then
                  begin
                    Format.pp_print_string fmt ";";
                    Format.pp_print_space fmt ();
                  end;
                pp desc printers fmt value;
                true in
              ignore (List.fold_left pp_value false list);
              Format.pp_print_string fmt "]";
              Format.pp_close_box fmt ();
          | None ->
              let head, (tail, ()) = destruct.values in
              Format.pp_open_box fmt 0;
              pp head_desc printers' fmt head;
              Format.pp_print_string fmt " ::";
              Format.pp_print_space fmt ();
              pp tail_desc printers' fmt tail;
              Format.pp_close_box fmt ();
          end
      | _ ->
          Format.pp_open_box fmt 0;
          Format.pp_print_string fmt destruct.name;
          begin match destruct.kind with
          | Tuple { structure = []; _ } -> ()
          | Tuple tuple ->
              Format.pp_print_space fmt ();
              pp_tuple printers' tuple
          | Record record ->
              Format.pp_print_space fmt ();
              pp_record printers' record
          end;
          Format.pp_close_box fmt ();
      end
  | Variant { constructors; destruct; _ } ->
      let Destruct destruct = Variant.destruct constructors (destruct x) in
      begin match destruct.kind with
      | Constructor { name; argument } ->
          Format.pp_open_box fmt 0;
          Format.pp_print_string fmt "`";
          Format.pp_print_string fmt name;
          begin match argument with
          | None -> ()
          | Some { desc; value } ->
              Format.pp_print_space fmt ();
              Format.pp_print_string fmt "(";
              pp desc printers fmt value;
              Format.pp_print_string fmt ")";
          end;
          Format.pp_close_box fmt ()
      | Inherit { desc; value } ->
          pp desc printers fmt value
      end
  | Object _ ->
      Format.pp_print_string fmt "<obj>"
  | Tuple { structure; destruct; _ } ->
      pp_tuple printers
        { structure = Tuple.of_desc structure; values = destruct x }
  | Record { structure; destruct; _ } ->
      pp_record printers { structure; values = destruct x }
  | Lazy desc ->
      if Lazy.is_val x then
        begin
          Format.pp_open_box fmt 1;
          Format.pp_print_string fmt "lazy (";
          pp desc printers fmt (Lazy.force x);
          Format.pp_print_string fmt ")";
          Format.pp_close_box fmt ()
        end
      else
        Format.pp_print_string fmt "<lazy>"
  | Apply { arguments; desc; transfer } ->
      let printers =
        Printers.make { f = pp } arguments transfer printers in
      pp desc printers fmt x
  | Rec { desc; _ } ->
      pp desc printers fmt x
  | RecArity { desc } ->
      pp desc printers fmt x
  | Opaque _ | MapOpaque ->
      Format.pp_print_string fmt "<opaque>"
  | SelectGADT { desc; _ } ->
      pp desc printers fmt x
  | SubGADT { desc; _ } ->
      pp desc printers fmt x
  | Attributes { attributes; desc } ->
      begin match attributes.typed Attribute_printer with
      | Some printer ->
          printer fmt x
      | None ->
          match attributes.typed Attribute_polyprinter with
          | Some printer ->
              let printers =
                Printers.to_sequence (Some ({ item = fun _ _ -> assert false }))
                  printers in
              printer printers fmt x
          | None ->
              pp desc printers fmt x
      end
  | Name { desc; _ } ->
      pp desc printers fmt x
  | _ -> .

let show desc printers x =
  Format.asprintf "%a" (pp desc printers) x
