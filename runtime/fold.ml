open Desc

open Tools

module Fold = struct
  type ('a, 'b) t = 'a -> 'b -> 'b
end

module Folds = ParameterizedVector (Fold)

let fold :
  type a structure arity rec_arity positive negative direct gadt .
  (a, structure, arity, rec_arity, 'kinds, positive, negative, direct, gadt)
    desc -> (arity, 'acc, direct) Folds.t -> (a, 'acc) Fold.t =
fun (type acc) desc folds x (acc : acc) ->
  let module Vector = Folds.Unary (struct type t = acc end) in

let rec fold :
  type a structure arity rec_arity positive negative direct gadt .
  (a, structure, arity, rec_arity, 'kinds, positive, negative, direct, gadt)
    desc -> (arity, direct) Vector.t -> (a, acc) Fold.t =
fun desc folds x acc ->

  let fold_tuple folds tuple acc =
    let fold_tuple_item (Tuple.Fold { desc; value; _ }) acc =
      fold desc folds value acc in
    Tuple.fold fold_tuple_item tuple acc in

  let fold_record folds record acc =
    let fold_record_field (Record.Fold { field; value; _ }) acc =
      let fold_field _label desc folds value acc =
        fold desc folds value acc in
      match field with
      | Poly { label; destruct; variables; _ } ->
          let MakeAppend subarity = make_append variables.direct_count in
          let folds =
            folds |>
            Vector.append None
              variables.presences variables.direct_count variables.direct
              variables.direct_count subarity in
          let ForallDestruct { desc; destruct } =
            destruct.forall_destruct variables.direct_count subarity in
          fold_field label desc folds (destruct value) acc
      | Mono { label; desc; _ } -> fold_field label desc folds value acc in
    Record.fold fold_record_field record acc in

  match desc with
  | Variable index ->
      Vector.get index folds x acc
  | Builtin _ | Arrow _ | LabelledArrow _ -> acc
  | Array desc ->
      Array.fold_left (fun acc x -> fold desc folds x acc) acc x
  | Constr { constructors; destruct; _ } ->
      let Destruct destruct =
        Constructor.destruct constructors (destruct x) in
      let folds' =
        match destruct.link with
        | Exists { exists_count; exists; variables; _ } ->
            folds |>
            Vector.append
              (Some { item = fun _ acc -> acc })
              variables.presences variables.direct_count variables.direct
              exists_count exists
        | Constructor -> folds in
      begin match destruct.kind with
      | Tuple tuple ->
          fold_tuple folds' tuple acc
      | Record record ->
          fold_record folds' record acc
      end
  | Variant { constructors; destruct; _ } ->
      let Destruct destruct = Variant.destruct constructors (destruct x) in
      begin match destruct.kind with
      | Constructor { argument; _ }->
          begin match argument with
          | None -> acc
          | Some { desc; value } ->
              fold desc folds value acc
          end
      | Inherit { desc; value } ->
          fold desc folds value acc
      end
  | Object { methods; destruct; _ } ->
      let fold_object_item (Object.Fold { desc; method_; _ }) acc =
        fold desc folds (method_ ()) acc in
      Object.fold fold_object_item { structure = methods; methods = destruct x }
        acc
  | Tuple { structure; destruct; _ } ->
      fold_tuple folds
        { structure = Tuple.of_desc structure; values = destruct x } acc
  | Record { structure; destruct; _ } ->
      fold_record folds { structure; values = destruct x } acc
  | Lazy desc ->
      fold desc folds (Lazy.force x) acc
  | Apply { arguments; desc; transfer } ->
      let folds =
        Vector.make { f = fold } arguments transfer folds in
      fold desc folds x acc
  | Rec { desc; _ } ->
      fold desc folds x acc
  | RecArity { desc } ->
      fold desc folds x acc
  | Opaque _
  | MapOpaque -> acc
  | SelectGADT { desc; _ } ->
      fold desc folds x acc  | SubGADT { desc; _ } ->
      fold desc folds x acc
  | Attributes { desc; _ } ->
      fold desc folds x acc
  | _ -> . in
  fold desc (Vector.to_unary folds) x acc
