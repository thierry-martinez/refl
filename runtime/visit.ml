open Desc

open Tools

module type VisitorS = sig
  module Applicative : Traverse.Applicative.S

  val hook : 'a refl -> ('a -> 'a Applicative.t) -> 'a -> 'a Applicative.t
end

module type VisitS = sig
  module Visitor : UnaryTypeS

  module Visitors : VectorS with type 'a T.t = 'a Visitor.t

  val visit :
      ('a, 'structure, 'arity, 'rec_group, Kinds.visitable, 'positive,
        'negative, 'direct, 'gadt) desc -> ('arity, 'direct) Visitors.t ->
      'a Visitor.t
end

module Make (V : VisitorS) : VisitS
with type 'a Visitor.t = 'a -> 'a V.Applicative.t = struct
  module Visitor = struct
    type 'a t = 'a -> 'a V.Applicative.t
  end

  module Visitors = Vector (Visitor)

  let rec visit :
    type structure a arity rec_group positive negative direct gadt .
      (a, structure, arity, rec_group, [< Kinds.visitable] as 'kinds, positive,
        negative, direct, gadt) desc -> (arity, direct) Visitors.t ->
      a Visitor.t =
  fun a_struct visitors x ->
    let open V.Applicative in
    let rec visit_variant :
      type cases structures .
      (cases, structures, arity, rec_group, 'kinds, positive,
        negative, direct, gadt) variant_constructors ->
      cases choice Visitor.t =
    fun constructors choice ->
      match constructors, choice with
      | VCCons { tail = a_constructors; _ },
        CNext a_choice ->
          visit_variant a_constructors a_choice |> map @@ fun a_choice ->
          CNext a_choice
      | VCCons { head = VConstructor a; _ }, CFirst arguments ->
          begin match a.argument, arguments with
          | VNone, () ->
              pure (CFirst ())
          | VSome a, (value, ()) ->
              visit a visitors value |> map @@ fun value ->
              CFirst (value, ())
          end
      | VCCons { head = VInherit a; _ }, CFirst value ->
          visit a visitors value |> map @@ fun value ->
          CFirst value
      | _ -> . in

    let rec visit_tuple :
      type types structures .
      (types, structures, arity, rec_group, 'kinds, positive, negative, direct,
        gadt) tuple_structure -> types Visitor.t =
    fun tuple types ->
      match tuple, types with
      | TNil, () -> pure ()
      | TCons a, (head, tail) ->
          apply (map (fun head tail -> (head, tail))
              (visit a.head visitors head))
            (fun () -> visit_tuple a.tail tail) in

    let rec visit_record :
      type types structures  .
      (types, structures, arity, rec_group, 'kinds, positive,
        negative, direct, gadt) record_structure ->
      types Visitor.t =
    fun tuple types ->
      match tuple, types with
      | RNil, () -> pure ()
      | RCons a, (head, tail) ->
          let Mono a_head = a.head in
          apply (map (fun head tail -> (head, tail))
             (visit a_head.desc visitors head))
           (fun () -> visit_record a.tail tail) in

    let visit_kind :
      type types structure .
      (types, structure, arity, rec_group, 'kinds, positive, negative, direct,
        gadt) constructor_kind -> types Visitor.t =
    fun a values ->
      match a with
      | CTuple t -> visit_tuple t values
      | CRecord r -> visit_record r values in

    let rec visit_constr :
      type cases structures .
      (cases, structures, arity, rec_group, 'kinds, positive, negative, direct,
        gadt) constructors -> cases binary_choice Visitor.t =
    fun constructors choice ->
      match constructors, choice with
      | CNode a, CZero choice ->
          visit_constr a.zero choice |> map @@ fun choice ->
          CZero choice
      | CNode a, COne choice ->
          visit_constr a.one choice |> map @@ fun choice ->
          COne choice
      | CLeaf (Constructor a), CEnd (values, eqs) ->
          visit_kind a.kind values |> map @@ fun choice ->
          CEnd (choice, eqs) in

    match a_struct with
    | Variable a_index -> Visitors.get a_index visitors x
    | Builtin Bool -> pure x
    | Builtin Bytes -> pure x
    | Builtin Char -> pure x
    | Builtin Float -> pure x
    | Builtin Int -> pure x
    | Builtin Int32 -> pure x
    | Builtin Int64 -> pure x
    | Builtin Nativeint -> pure x
    | Builtin String -> pure x
    | Array desc ->
        let module M = Traverse.List (V.Applicative) in
        map Array.of_list
          (M.traverse (visit desc visitors) (Array.to_list x))
    | Constr c ->
        let x = c.destruct x in
        map c.construct (visit_constr c.constructors x)
    | Variant c ->
        let x = c.destruct x in
        map c.construct (visit_variant c.constructors x)
    | Tuple c ->
        let x = c.destruct x in
        map c.construct (visit_tuple c.structure x)
    | Record c ->
        let x = c.destruct x in
        map c.construct (visit_record c.structure x)
    | Apply a ->
        let visitors =
          Visitors.make { f = visit } a.arguments a.transfer visitors in
        visit a.desc visitors x
    | Rec { desc; _ } -> visit desc visitors x
    | RecGroup { desc; _ } -> visit desc visitors x
    | Opaque _ -> pure x
    | MapOpaque -> pure x
    | SelectGADT { desc; _ } -> visit desc visitors x
    | SubGADT { desc; _ } -> visit desc visitors x
    | Attributes { desc; _ } -> visit desc visitors x
    | Name n ->
        V.hook n.refl (visit n.desc visitors) x
    | _ -> .
end
