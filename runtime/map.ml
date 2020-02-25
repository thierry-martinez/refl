open Desc

open Tools

module Mapper = struct
  type ('a, 'b) t = 'a -> 'b
end

module Mappers = SignedVector (Mapper)

let rec map :
  type structure a_struct b_struct a_arity b_arity rec_group
        kinds positive negative direct gadt .
  (a_struct, structure, a_arity, rec_group, kinds, positive,
    negative, direct, gadt) desc ->
  (b_struct, structure, b_arity, rec_group, kinds, positive,
    negative, direct, gadt) desc ->
  (a_arity, b_arity, positive, negative) Mappers.t ->
  (a_struct, b_struct) Mapper.t =
fun a_struct b_struct mapping x ->
  let rec_map a_desc b_desc =
    map a_desc b_desc mapping in
  let module Mapper = struct
    type nonrec rec_group = rec_group
    type nonrec positive = positive
    type nonrec negative = negative
    type nonrec a_arity = a_arity
    type nonrec b_arity = b_arity
    type nonrec gadt = gadt
    type ('a_arity, 'b_arity, 'positive, 'negative) t =
        ('a_arity, 'b_arity, 'positive, 'negative) Mappers.t
    let initial = mapping
    let grow mapping :
        ('a_arity, 'b_arity, 'positive, 'negative) Mappers.t =
      Mappers.PN (Stdcompat.Fun.id, Stdcompat.Fun.id) :: mapping
    let map mapping desc_a desc_b x =
      map desc_a desc_b mapping x
  end in
  match a_struct, b_struct with
  | Variable a_index, Variable b_index ->
      Mappers.get a_index b_index mapping x
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
      Array.map (rec_map desc_a desc_b) x
  | Constr { constructors = a_constructors; destruct; _ },
    Constr { constructors = b_constructors; construct; _ } ->
      let module Map = Constructor.Map (Mapper) in
      destruct x |>
      Map.map_choice a_constructors b_constructors |>
      construct
  | Variant { constructors = a_constructors; destruct; _ },
    Variant { constructors = b_constructors; construct; _ } ->
      destruct x |>
      Variant.map_choice { f = rec_map } a_constructors b_constructors |>
      construct
  | Object a, Object b ->
      a.destruct x |>
      Object.map { f = rec_map } a.methods b.methods |>
      b.construct
  | Tuple { structure = a_structure; destruct; _ },
    Tuple { structure = b_structure; construct; _ } ->
      destruct x |>
      Tuple.map { f = rec_map } a_structure b_structure |>
      construct
  | Record { structure = a_structure; destruct; _ },
    Record { structure = b_structure; construct; _ } ->
      let module Map = Record.Map (Mapper) in
      destruct x |>
      Map.map a_structure b_structure |>
      construct
  | Lazy a_desc, Lazy b_desc ->
      lazy (map a_desc b_desc mapping (Lazy.force x))
  | Apply { arguments = a_arguments; desc = a_desc; transfer },
    Apply { arguments = b_arguments; desc = b_desc; _ } ->
      let mapping' =
        Mappers.make { f = map } a_arguments b_arguments transfer
          mapping in
      map a_desc b_desc mapping' x
  | Rec a, Rec b ->
      let Eq = selection_functional_head a.index b.index in
      map a.desc b.desc mapping x
  | RecGroup a, RecGroup b ->
      map a.desc b.desc mapping x
  | Opaque a, Opaque b ->
      map a.desc b.desc mapping x
  | MapOpaque, MapOpaque ->
      x
  | Arrow { parameter = a_parameter; result = a_result },
    Arrow { parameter = b_parameter; result = b_result } ->
      (fun parameter ->
        map a_result b_result mapping
          (x (map b_parameter a_parameter (Mappers.reverse mapping)
            parameter)))
  | LabelledArrow { parameter = a_parameter; result = a_result; unwrap; _ },
    LabelledArrow { parameter = b_parameter; result = b_result; wrap; _ } ->
      wrap (fun parameter ->
        map a_result b_result mapping
          (unwrap x
            (map b_parameter a_parameter (Mappers.reverse mapping)
            parameter)))
  | SelectGADT { index = index_a; desc = desc_a },
    SelectGADT { index = index_b; desc = desc_b } ->
      let Eq = selection_functional_head index_a index_b in
      map desc_a desc_b mapping x
  | SubGADT a, SubGADT b ->
      let Eq = sub_gadt_functional a.sub_gadt b.sub_gadt in
      map a.desc b.desc mapping x
  | Attributes a, Attributes b ->
      map a.desc b.desc mapping x
  | Name a, Name b ->
      map a.desc b.desc mapping x
  | _ -> .
