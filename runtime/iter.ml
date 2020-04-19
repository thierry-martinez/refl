open Desc

open Tools

module Iter = struct
  type 'a t = 'a -> unit
end

module Iters = Vector (Iter)

let rec iter :
  type a structure arity rec_group positive negative direct gadt .
  (a, structure, arity, rec_group, 'kinds, positive, negative, direct, gadt)
    desc -> (arity, direct) Iters.t -> a Iter.t =
fun desc iters x ->
  let iter_tuple iters tuple =
    let iter_tuple_item (Tuple.Fold { desc; value; _ }) () =
      iter desc iters value in
    Tuple.fold iter_tuple_item tuple () in

  let iter_record iters record =
    let iter_record_field (Record.Fold { field; value; _ }) () =
      match field with
      | Poly { destruct; variables; _ } ->
          let MakeAppend subarity = make_append variables.direct_count in
          let iters =
            iters |>
            Iters.append None
              variables.presences variables.direct_count variables.direct
              variables.direct_count subarity in
          let ForallDestruct { desc; destruct } =
            destruct.forall_destruct variables.direct_count subarity in
          iter desc iters (destruct value)
      | Mono { desc; _ } -> iter desc iters value in
    Record.fold iter_record_field record () in

  match desc with
  | Variable index ->
      Iters.get index iters x
  | Builtin _ -> ()
  | Arrow _ -> ()
  | LabelledArrow _ -> ()
  | Array desc ->
      Array.iter (iter desc iters) x
  | Constr { constructors; destruct; _ } ->
      let Constructor.Destruct destruct =
        Constructor.destruct constructors (destruct x) in
      let iters' =
        match destruct.link with
        | Constructor.Exists { exists_count; exists; variables; _ } ->
            iters |>
            Iters.append
              (Some { item = fun _ -> () })
              variables.presences variables.direct_count variables.direct
              exists_count exists
        | Constructor.Constructor -> iters in
      begin match destruct.kind with
      | Constructor.Tuple tuple ->
          iter_tuple iters' tuple
      | Constructor.Record record ->
          iter_record iters' record
      end
  | Variant { constructors; destruct; _ } ->
      let Variant.Destruct destruct =
        Variant.destruct constructors (destruct x) in
      begin match destruct.kind with
      | Variant.Constructor { argument; _ }->
          begin match argument with
          | Variant.None -> ()
          | Variant.Some { desc; value } ->
              iter desc iters value;
          end
      | Variant.Inherit { desc; value } ->
          iter desc iters value
      end
  | Object { methods; destruct; _ } ->
      let iter_object_item (Object.Fold { desc; method_; _ }) () =
        iter desc iters (method_ ()) in
      Object.fold iter_object_item { structure = methods; methods = destruct x }
        ()
  | Tuple { structure; destruct; _ } ->
      iter_tuple iters
        { structure = Tuple.of_desc structure; values = destruct x }
  | Record { structure; destruct; _ } ->
      iter_record iters { structure; values = destruct x }
  | Lazy desc ->
      iter desc iters (Lazy.force x)
  | Apply { arguments; desc; transfer } ->
      let iters =
        Iters.make { f = iter } arguments transfer iters in
      iter desc iters x
  | Rec { desc; _ } ->
      iter desc iters x
  | RecGroup { desc } ->
      iter desc iters x
  | MapOpaque _ -> ()
  | Opaque _ -> ()
  | SelectGADT { desc; _ } ->
      iter desc iters x
  | SubGADT { desc; _ } ->
      iter desc iters x
  | Attributes { desc; _ } ->
      iter desc iters x
  | Name { desc; _ } ->
      iter desc iters x
  | _ -> .
