open Desc

module StringMap = Stdcompat.Map.Make (String)

type ('a, 'arity, 'b) typed_attribute_kind +=
  | Attribute_default : ('a, 'arity, 'a) typed_attribute_kind

type ('arity, 'rec_group, 'kinds, 'positive, 'negative, 'direct, 'gadt) field =
  | F :
    ('a, 'structure, 'arity, 'rec_group, 'kinds, 'positive, 'negative, 'direct,
        'gadt) desc * 'a ->
      ('arity, 'rec_group, 'kinds, 'positive, 'negative, 'direct, 'gadt) field

let rec make_fields :
  type types structures .
  (types, structures, 'arity, 'rec_group, 'kinds, 'positive,
    'negative, 'direct, 'gadt) record_structure ->
  ('arity, 'rec_group, 'kinds, 'positive, 'negative, 'direct, 'gadt)
    field StringMap.t ->
  types =
fun structures fields ->
  match structures with
  | RNil -> ()
  | RCons { head = Poly _; _ } ->
      invalid_arg "make: polymorphic fields unsupported"
  | RCons { head = Mono head; tail } ->
      let head =
        match StringMap.find_opt head.label fields with
        | None ->
            begin match head.attributes.typed Attribute_default with
            | Some default -> default
            | None ->
                invalid_arg
                  (Printf.sprintf "make: no value for field '%s'" head.label)
            end
        | Some (F (desc, value)) ->
            match Convert.cast desc head.desc value with
            | exception Convert.Incompatible ->
                invalid_arg
                  (Printf.sprintf "make: invalid value type for field '%s'"
                     head.label);
            | value -> value in
      head, make_fields tail fields

type ('a, 'b) record_type_structure =
    [`RecGroup of [`Name of [`Record of 'a]] * 'b]

let make :
  type a structures new_rec_group .
  (a, (structures, new_rec_group) record_type_structure, 'arity,
    'rec_group, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  ('arity, new_rec_group, 'kinds, 'positive, 'negative, 'direct, 'gadt)
    field StringMap.t ->
  a =
fun desc fields ->
  let RecGroup { desc = Name { desc =
      Record { structure; construct; _ }; _ }; _ } =
    desc in
  construct (make_fields structure fields)
