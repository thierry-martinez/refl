open Desc

open Tools

exception Incompatible

let selection :
    type index_a index_b sequence head_a head_b tail_a tail_b .
    ([`Succ of index_a], sequence, head_a, tail_a) selection ->
    ([`Succ of index_b], sequence, head_b, tail_b) selection ->
    (head_a, head_b) eq =
fun selection_a selection_b ->
  match compare_selection selection_a selection_b with
  | LessThan | GreaterThan -> raise Incompatible
  | Equal Eq ->
      let Eq = selection_functional_head selection_a selection_b in
      Eq

let rec convert_eqs :
  type a_eqs structure_eqs_a structure_eqs_b b_eqs kinds_a kinds_b .
  (a_eqs, structure_eqs_a, kinds_a, 'gadt) constructor_eqs ->
  (b_eqs, structure_eqs_b, kinds_b, 'gadt) constructor_eqs ->
  a_eqs -> b_eqs =
fun a_eqs b_eqs eqs ->
  match a_eqs, b_eqs, eqs with
  | ENil, ENil, () -> ()
  | ECons { head = head_a; tail = tail_a },
    ECons { head = head_b; tail = tail_b },
    (eq, eq_tail) ->
      let Eq = selection head_a head_b in
      (eq, convert_eqs tail_a tail_b eq_tail)
  | _ -> raise Incompatible

let convert_presence :
  type global_a local_a global_b local_b .
  (global_a, local_a) presence ->
  (global_b, local_b) presence ->
  (local_a, local_b) eq =
fun presence_a presence_b ->
  match presence_a, presence_b with
  | Present, Present -> Eq
  | Absent, Absent -> Eq
  | _ -> raise Incompatible

let rec convert_presences :
  type global local_a local_b .
  (global, local_a) presences ->
  (global, local_b) presences ->
  (local_a, local_b) eq =
fun presences_a presences_b ->
  match presences_a, presences_b with
  | Presences, Presences -> Eq
  | AddPresent presences_a, AddPresent presences_b ->
      let Eq = convert_presences presences_a presences_b in
      Eq
  | AddAbsent presences_a, AddAbsent presences_b ->
      let Eq = convert_presences presences_a presences_b in
      Eq
  | _ -> raise Incompatible

module Converter = struct
  type ('a, 'b) t = 'a -> 'b
end

module Converters = struct
  type ('a, 'b) item = ('a, 'b) Converter.t * ('b, 'a) Converter.t

  type ('a, 'b) t =
    | [] : (unit, unit) t
    | (::) : ('a, 'b) item * ('at, 'bt) t -> ('a * 'at, 'b * 'bt) t

  let rec get :
    type index arity_a a positive_a direct_a arity_b b positive_b direct_b .
    (index, arity_a, a, positive_a, direct_a) variable ->
    (index, arity_b, b, positive_b, direct_b) variable ->
    (arity_a, arity_b) t -> a -> b =
  fun index_a index_b converters ->
    match index_a, index_b, converters with
    | VFirst, VFirst, (converter, _) :: _ -> converter
    | VNext index_a, VNext index_b, _ :: tail -> get index_a index_b tail

  let rec reverse :
    type arity_a arity_b . (arity_a, arity_b) t -> (arity_b, arity_a) t =
  fun converters ->
    match converters with
    | [] -> []
    | (p, n) :: tl -> (n, p) :: reverse tl
end

type ('arity_a, 'arity_b) converters =
  | SameArity of ('arity_a, 'arity_b) eq
  | Converters of ('arity_a, 'arity_b) Converters.t

type ('forall, 'arity_a, 'arity_b) make_variables =
  | MakeVariables : {
        subarity_a : ('forall, 'arity_a, 'subarity_a) append;
        subarity_b : ('forall, 'arity_b, 'subarity_b) append;
        converters : ('subarity_a, 'subarity_b) converters
      } -> ('forall, 'arity_a, 'arity_b) make_variables

let reverse :
  type arity_a arity_b .
  (arity_a, arity_b) converters ->
  (arity_b, arity_a) converters =
fun converters ->
  match converters with
  | SameArity Eq -> SameArity Eq
  | Converters converters -> Converters (Converters.reverse converters)

let rec make_variables :
  type count forall arity_a arity_b .
  (count, forall) length ->
  (arity_a, arity_b) converters ->
  (forall, arity_a, arity_b) make_variables =
fun count converters ->
  match count with
  | Zero -> MakeVariables { subarity_a = Nil; subarity_b = Nil; converters }
  | Succ count ->
      let MakeVariables { subarity_a; subarity_b; converters } =
        make_variables count converters in
      MakeVariables {
        subarity_a = Add subarity_a;
        subarity_b = Add subarity_b;
        converters =
          match converters with
          | SameArity Eq -> SameArity Eq
          | Converters converters ->
              Converters ((Stdcompat.Fun.id, Stdcompat.Fun.id) :: converters)
      }

let rec convert :
  type structure_a structure_b a_struct b_struct arity_a arity_b rec_group_a
    rec_group_b kinds_a kinds_b positive_a negative_a direct_a positive_b
    negative_b direct_b gadt_a gadt_b .
  (a_struct, structure_a, arity_a, rec_group_a,
    kinds_a, positive_a, negative_a, direct_a, gadt_a) desc ->
  (b_struct, structure_b, arity_b, rec_group_b,
    kinds_b, positive_b, negative_b, direct_b, gadt_b) desc ->
  (arity_a, arity_b) converters ->
  (gadt_a, gadt_b) eq option ->
  (a_struct, b_struct) Converter.t =
fun a_struct b_struct converters eq_gadt x ->
  let rec convert_tuple :
    type a_types b_types structures_a structures_b
      positive_a negative_a direct_a positive_b negative_b direct_b
      gadt_a gadt_b arity_a arity_b .
    (a_types, structures_a, arity_a, rec_group_a,
      kinds_a, positive_a, negative_a, direct_a, gadt_a) tuple_structure ->
    (b_types, structures_b, arity_b, rec_group_b,
      kinds_b, positive_b, negative_b, direct_b, gadt_b) tuple_structure ->
    (arity_a, arity_b) converters ->
      (gadt_a, gadt_b) eq option ->
    a_types -> b_types =
  fun a_tuple b_tuple converters eq_gadt a_types ->
    match a_tuple, b_tuple, a_types with
    | TNil, TNil, () -> ()
    | TCons a, TCons b, (head, tail) ->
        (convert a.head b.head converters eq_gadt head,
          convert_tuple a.tail b.tail converters eq_gadt tail)
    | _ -> raise Incompatible in

  let convert_poly :
    type a b structure_a structure_b count_a count_b
      positive_a negative_a direct_a positive_b negative_b direct_b
      positives_a negatives_a directs_a
      positives_b negatives_b directs_b
      subpositive_a subnegative_a subdirect_a
      subpositive_b subnegative_b subdirect_b gadt_a gadt_b arity_a
      arity_b .
    (count_a, [`Absent], positive_a, negative_a, direct_a, positives_a,
      negatives_a, directs_a, subpositive_a, subnegative_a, subdirect_a)
      subvariables ->
    (count_b, [`Absent], positive_b, negative_b, direct_b, positives_b,
      negatives_b, directs_b, subpositive_b, subnegative_b, subdirect_b)
      subvariables ->
    (a, structure_a, arity_a, rec_group_a, kinds_a, subpositive_a,
      subnegative_a, subdirect_a, gadt_a, count_a) forall_destruct ->
    ((b, structure_b, arity_b, rec_group_b,
      kinds_b, subpositive_b, subnegative_b, subdirect_b, gadt_b,
      count_b) forall_construct -> b) ->
    (arity_a, arity_b) converters ->
    (gadt_a, gadt_b) eq option ->
    a -> b =
  fun subvariables_a _subvariables_b destruct_a construct_b converters eq_gadt
      value ->
    let forall_construct :
      type forall b subarity_b .
      (count_b, forall) length ->
      (forall, arity_b, subarity_b) append ->
      (b, _, subarity_b, rec_group_b, kinds_b, subpositive_b, subnegative_b,
        subdirect_b, gadt_b) desc ->
      b =
    fun count subarity_b desc_b ->
      match compare_length count subvariables_a.positive_count with
      | LessThan | GreaterThan -> raise Incompatible
      | Equal Eq ->
          let MakeAppend arity_a = make_append count in
          let ForallDestruct { desc = desc_a; destruct } =
            destruct_a.forall_destruct count arity_a in
          let MakeVariables { converters; subarity_a;
              subarity_b = subarity_b' } =
            make_variables count converters in
          let Eq = append_functional arity_a subarity_a in
          let Eq = append_functional subarity_b subarity_b' in
          convert desc_a desc_b converters eq_gadt (destruct value) in
    construct_b { forall_construct } in

  let rec convert_record :
    type a_types b_types structures_a structures_b
      positive_a negative_a direct_a positive_b negative_b direct_b
      gadt_a gadt_b arity_a arity_b .
    (a_types, structures_a, arity_a, rec_group_a, kinds_a, positive_a,
      negative_a, direct_a, gadt_a) record_structure ->
    (b_types, structures_b, arity_b, rec_group_b, kinds_b, positive_b,
      negative_b, direct_b, gadt_b) record_structure ->
    (arity_a, arity_b) converters ->
    (gadt_a, gadt_b) eq option ->
    a_types -> b_types =
  fun a_tuple b_tuple converters eq_gadt a_types ->
    match a_tuple, b_tuple, a_types with
    | RNil, RNil, () -> ()
    | RCons a, RCons b, (head, tail) ->
        let head =
          match a.head, b.head with
          | Mono a, Mono b ->
              convert a.desc b.desc converters eq_gadt head
          | Poly a, Poly b ->
              convert_poly a.variables b.variables a.destruct b.construct
                converters eq_gadt head
          | _ -> raise Incompatible in
        (head, convert_record a.tail b.tail converters eq_gadt tail)
    | _ -> raise Incompatible in

  let convert_kind :
    type types_a types_b arity_a arity_b structure_a structure_b
      positive_a negative_a direct_a positive_b negative_b direct_b.
    (types_a, structure_a, arity_a, rec_group_a, kinds_a, positive_a,
      negative_a, direct_a, gadt_a) constructor_kind ->
    (types_b, structure_b, arity_b, rec_group_b, kinds_b, positive_b,
      negative_b, direct_b, gadt_b) constructor_kind ->
    (arity_a, arity_b) converters ->
    (gadt_a, gadt_b) eq option ->
    types_a -> types_b =
  fun a b converters eq_gadt values ->
    match a, b with
    | CTuple a_tuple, CTuple b_tuple ->
        convert_tuple a_tuple b_tuple converters eq_gadt values
    | CRecord a_record, CRecord b_record ->
        convert_record a_record b_record converters eq_gadt values
    | _ -> raise Incompatible in

  let rec convert_constructor :
    type a_cases b_cases structures_a structures_b .
    (a_cases, structures_a, arity_a, rec_group_a, kinds_a, positive_a,
      negative_a, direct_a, gadt_a) constructors ->
    (b_cases, structures_b, arity_b, rec_group_b, kinds_b, positive_b,
      negative_b, direct_b, gadt_b) constructors ->
    a_cases binary_choice -> b_cases binary_choice =
  fun a_constructors b_constructors a_choice ->
    match a_constructors, b_constructors, a_choice with
    | CNode a, CNode b, CZero a_choice ->
        CZero (convert_constructor a.zero b.zero a_choice)
    | CNode a, CNode b, COne a_choice ->
        COne (convert_constructor a.one b.one a_choice)
    | CLeaf (Constructor a), CLeaf (Constructor b), CEnd (values, eqs) ->
        begin match eq_gadt with
        | None -> raise Incompatible
        | Some Eq ->
            let eqs = convert_eqs a.eqs b.eqs eqs in
            CEnd (convert_kind a.kind b.kind converters (Some Eq) values, eqs)
        end
    | CLeaf (Exists a), CLeaf (Exists b), CEnd values ->
        begin match eq_gadt with
        | None -> raise Incompatible
        | Some Eq ->
            let Eq = selection a.selection b.selection in
            let ExistsDestruct a' = a.destruct values in
            let Eq = convert_presence a.presence b.presence in
            begin match compare_length a'.exists_count
                b.variables.positive_count with
            | LessThan | GreaterThan -> raise Incompatible
            | Equal Eq ->
                let MakeVariables { converters; subarity_a; subarity_b } =
                  make_variables a'.exists_count converters in
                let ExistsConstruct b' =
                  b.construct a'.exists_count a'.constraints subarity_b in
                let Eq = append_functional a'.exists subarity_a in
                let values =
                  convert_kind a'.kind b'.kind converters (Some Eq) a'.values |>
                  b'.construct in
                CEnd values
            end
        end
    | _ -> raise Incompatible in

  let rec convert_variant :
    type a_cases b_cases structures_a structures_b .
    (a_cases, structures_a, arity_a, rec_group_a, kinds_a, positive_a,
      negative_a, direct_a, gadt_a) variant_constructors ->
    (b_cases, structures_b, arity_b, rec_group_b, kinds_b, positive_b,
      negative_b, direct_b, gadt_b) variant_constructors ->
    a_cases choice -> b_cases choice =
  fun a_constructors b_constructors a_choice ->
    match a_constructors, b_constructors, a_choice with
    | VCCons { tail = a_constructors; _ },
      VCCons { tail = b_constructors; _ },
      CNext a_choice ->
        CNext
          (convert_variant a_constructors b_constructors a_choice)
    | VCCons { head = VConstructor a; _ },
      VCCons { head = VConstructor b; _ },
      CFirst arguments ->
        CFirst begin
          match a.argument, b.argument, arguments with
          | VNone, VNone, () -> ()
          | VSome a, VSome b, (value, ()) ->
              (convert a b converters eq_gadt value, ())
          | _ -> raise Incompatible
        end
    | VCCons { head = VInherit a; _ },
      VCCons { head = VInherit b; _ },
      CFirst value ->
        CFirst (convert a b converters eq_gadt value)
    | _ -> raise Incompatible in

  let rec convert_object :
    type a_types b_types structures_a structures_b
      positive_a negative_a direct_a positive_b negative_b direct_b .
    (a_types, structures_a, arity_a, rec_group_a, kinds_a, positive_a,
      negative_a, direct_a, gadt_a) object_methods ->
    (b_types, structures_b, arity_b, rec_group_b, kinds_b, positive_b,
      negative_b, direct_b, gadt_b) object_methods ->
    a_types Delays.t -> b_types Delays.t =
  fun methods_a methods_b a ->
    let open Delays in
    match methods_a, methods_b, a with
    | ONil, ONil, [] -> []
    | OCons a, OCons b, head :: tail ->
        let OMethod a' = a.head in
        let OMethod b' = b.head in
        (fun () -> convert a'.desc b'.desc converters eq_gadt (head ())) ::
        convert_object a.tail b.tail tail
    | _ -> raise Incompatible in

  match a_struct, b_struct with
  | Variable a_index, Variable b_index ->
      begin match equal_variable a_index b_index with
      | Error () -> raise Incompatible
      | Ok Eq ->
          match converters with
          | SameArity Eq ->
              let Eq = variable_functional a_index b_index in
              x
          | Converters converters -> Converters.get a_index b_index converters x
      end
  | Builtin Bool, Builtin Bool -> x
  | Builtin Bytes, Builtin Bytes -> x
  | Builtin Char, Builtin Char -> x
  | Builtin Float, Builtin Float -> x
  | Builtin Int, Builtin Int -> x
  | Builtin Int32, Builtin Int32 -> x
  | Builtin Int64, Builtin Int64 -> x
  | Builtin Nativeint, Builtin Nativeint -> x
  | Builtin String, Builtin String -> x
  | Array desc_a, Array desc_b ->
      Array.map (convert desc_a desc_b converters eq_gadt) x
  | Constr { constructors = a_constructors; destruct; _ },
    Constr { constructors = b_constructors; construct; _ } ->
      destruct x |>
      convert_constructor a_constructors b_constructors |>
      construct
  | Variant { constructors = a_constructors; destruct; _ },
    Variant { constructors = b_constructors; construct; _ } ->
      destruct x |>
      convert_variant a_constructors b_constructors |>
      construct
  | Object a, Object b ->
      a.destruct x |>
      convert_object a.methods b.methods |>
      b.construct
  | Tuple { structure = a_structure; destruct; _ },
    Tuple { structure = b_structure; construct; _ } ->
      destruct x |>
      convert_tuple a_structure b_structure converters eq_gadt |>
      construct
  | Record { structure = a_structure; destruct; _ },
    Record { structure = b_structure; construct; _ } ->
      destruct x |>
      convert_record a_structure b_structure converters eq_gadt |>
      construct
  | Lazy a_desc, Lazy b_desc ->
      lazy (convert a_desc b_desc converters
         begin match eq_gadt with None -> None | Some Eq -> Some Eq end
         (Lazy.force x))
  | Apply a, Apply b ->
      let converters = transfer a.arguments b.arguments converters eq_gadt in
      convert a.desc b.desc (Converters converters) eq_gadt x
  | Rec a, Rec b ->
      convert a.desc b.desc converters eq_gadt x
  | RecGroup a, RecGroup b ->
      convert a.desc b.desc converters eq_gadt x
  | Opaque a, Opaque b ->
      convert a.desc b.desc converters eq_gadt x
  | Arrow a, Arrow b ->
      (fun parameter ->
        convert b.parameter a.parameter (reverse converters)
          begin match eq_gadt with None -> None | Some Eq -> Some Eq end
          parameter
        |> x |>
        convert a.result b.result converters eq_gadt)
  | LabelledArrow a, LabelledArrow b ->
      b.wrap (fun parameter ->
        convert b.parameter a.parameter (reverse converters)
          begin match eq_gadt with None -> None | Some Eq -> Some Eq end
          parameter
        |> a.unwrap x |>
        convert a.result b.result converters eq_gadt)
  | SubGADT a, SubGADT b ->
      convert a.desc b.desc converters begin
        match eq_gadt with
        | None -> None
        | Some Eq ->
            let Eq = sub_gadt_functional a.sub_gadt b.sub_gadt in
            Some Eq
      end x
  | Name a, _ ->
      convert a.desc b_struct converters eq_gadt x
  | _, Name b ->
      convert a_struct b.desc converters eq_gadt x
  | _ -> raise Incompatible

and transfer :
  type a structures_a arity_a rec_group_a kinds_a variables_a gadt_a
    b structures_b arity_b rec_group_b kinds_b variables_b gadt_b .
  (a, structures_a, arity_a, rec_group_a, kinds_a, variables_a,
    gadt_a) vector ->
  (b, structures_b, arity_b, rec_group_b, kinds_b, variables_b,
    gadt_b) vector ->
  (arity_a, arity_b) converters ->
  (gadt_a, gadt_b) eq option ->
  (a, b) Converters.t =
fun arguments_a arguments_b converters eq_gadt ->
  match arguments_a, arguments_b with
  | VNil, VNil -> []
  | VCons a, VCons b ->
      (convert a.head b.head converters eq_gadt,
        convert b.head a.head (reverse converters)
         begin match eq_gadt with None -> None | Some Eq -> Some Eq end) ::
      transfer a.tail b.tail converters eq_gadt
  | _ -> raise Incompatible

let cast a b x =
  convert a b (SameArity Eq) (Some Eq) x
