open Desc

open Tools

module Hasher = struct
  type 'a t = 'a -> int
end

module Hashers = Vector (Hasher)

let hash_pair : int * int -> int = Hashtbl.hash

let rec hash :
  type a structure arity rec_group positive negative direct gadt .
  (a, structure, arity, rec_group, [< Kinds.comparable], positive, negative,
      direct, gadt) desc -> (arity, direct) Hashers.t -> a Hasher.t =
fun desc hashers ->
  let hash_tuple hashers tuple =
    let hash_tuple_item (Tuple.Fold { desc; value; _ }) accu =
      hash_pair (accu, hash desc hashers value) in
    Tuple.fold hash_tuple_item tuple 0 in

  let hash_record :
    type values structures arity rec_group positive negative direct .
      (arity, direct) Hashers.t ->
        (values, structures, arity, rec_group,
         [< Kinds.comparable],
         positive, negative, direct, gadt) Record.t -> int =
  fun hashers record ->
    let hash_record_field :
        type types structures rec_group positive negative gadt .
        (types, structures, arity, rec_group, [< Kinds.comparable],
           positive, negative, direct, gadt) Record.fold -> int -> int =
   fun (Record.Fold { field; value; _ }) accu ->
      let h =
        match field with
        | Mono { desc; _ } -> hash desc hashers value in
      hash_pair (accu, h) in
    Record.fold hash_record_field record 0 in

  match desc with
  | Variable index ->
      Hashers.get index hashers
  | Builtin _ -> Hashtbl.hash
  | Array desc ->
      Array.fold_left
        (fun accu arg -> hash_pair (accu, hash desc hashers arg))
        0
  | Constr { constructors; destruct; _ } -> fun x ->
      let Constructor.Destruct destruct =
        Constructor.destruct constructors (destruct x) in
      let hashers' =
        match destruct.link with
        | Constructor.Exists {
              presence = Absent; exists_count; exists; variables; _ } ->
            hashers |>
            Hashers.append
              None
              variables.presences variables.direct_count variables.direct
              exists_count exists
        | Constructor.Constructor -> hashers in
      let argument =
        match destruct.kind with
        | Constructor.Tuple tuple ->
            hash_tuple hashers' tuple
        | Constructor.Record record ->
            hash_record hashers' record in
      hash_pair (int_of_binary_selection destruct.index, argument)
  | Variant { constructors; destruct; _ } -> fun x ->
      let Variant.Destruct destruct =
        Variant.destruct constructors (destruct x) in
      let argument =
        match destruct.kind with
        | Variant.Constructor { argument; _ }->
            begin match argument with
            | Variant.None -> 0
            | Variant.Some { desc; value } ->
                hash desc hashers value;
            end
        | Variant.Inherit { desc; value } ->
            hash desc hashers value in
      hash_pair (int_of_selection destruct.index, argument)
  | Object { methods; destruct; _ } -> fun x ->
      let hash_object_item (Object.Fold { desc; method_; _ }) accu =
        hash_pair (accu, hash desc hashers (method_ ())) in
      Object.fold hash_object_item
        { structure = methods; methods = destruct x } 0
  | Tuple { structure; destruct; _ } -> fun x ->
      hash_tuple hashers
        { structure = Tuple.of_desc structure; values = destruct x }
  | Record { structure; destruct; _ } -> fun x ->
      hash_record hashers { structure; values = destruct x }
  | Lazy desc -> fun x ->
      hash desc hashers (Lazy.force x)
  | Apply { arguments; desc; transfer } ->
      let hashers =
        Hashers.make { f = hash } arguments transfer hashers in
      hash desc hashers
  | Rec { desc; _ } ->
      hash desc hashers
  | RecGroup { desc } ->
      hash desc hashers
  | MapOpaque _ -> fun _ -> 0
  | Opaque _ -> fun _ -> 0
  | SelectGADT { desc; _ } ->
      hash desc hashers
  | SubGADT { desc; _ } ->
      hash desc hashers
  | Attributes { desc; _ } ->
      hash desc hashers
  | Name { desc; _ } ->
      hash desc hashers
  | _ -> .
