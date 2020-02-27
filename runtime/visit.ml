open Desc

open Tools

module type FunctorS = sig
  type 'a t

  val map : ('a -> 'b) -> 'a t -> 'b t
end

module type ApplicativeS = sig
  include FunctorS

  val pure : 'a -> 'a t

  val apply : ('a -> 'b) t -> 'a t -> 'b t
end

module ListTraverse (Applicative : ApplicativeS) = struct
  open Applicative

  let rec traverse (f : 'a -> 'b t) (a : 'a list) : 'b list t =
    match a with
    | [] -> pure []
    | hd :: tl ->
        apply (map List.cons (f hd)) (traverse f tl)
end

module Iter : ApplicativeS with type 'a t = unit = struct
  type 'a t = unit

  let map _f () = ()

  let pure _x = ()

  let apply _f () = ()
end

module Map : ApplicativeS with type 'a t = 'a = struct
  type 'a t = 'a

  let map f x = f x

  let pure x = x

  let apply f = f
end

module type MonoidS = sig
  type t

  val zero : t

  val ( + ) : t -> t -> t
end

module Reduce (Monoid : MonoidS)
  : ApplicativeS with type 'a t = Monoid.t = struct
  type 'a t = Monoid.t

  let map _f accu =
    accu

  let pure _x =
    Monoid.zero

  let apply = Monoid.( + )
end

module ReduceT (Monoid : MonoidS) (Base : ApplicativeS)
  : ApplicativeS with type 'a t = 'a Base.t * Monoid.t = struct
  type 'a t = 'a Base.t * Monoid.t

  let map f (x, a) =
    (Base.map f x, a)

  let pure x =
    (Base.pure x, Monoid.zero)

  let apply (f, a) (x, b) =
    (Base.apply f x, Monoid.(a + b))
end

module EnvT (Env : TypeS) (Base : ApplicativeS)
  : ApplicativeS with type 'a t = Env.t -> 'a Base.t = struct
  type 'a t = Env.t -> 'a Base.t

  let map f x env =
    Base.map f (x env)

  let pure x _env =
    Base.pure x

  let apply f x env =
    Base.apply (f env) (x env)
end

module Env (Env : TypeS)
  : ApplicativeS with type 'a t = Env.t -> unit = EnvT (Env) (Iter)

module Fold (Accu : TypeS)
  : ApplicativeS with type 'a t = Accu.t -> Accu.t = struct
  type 'a t = Accu.t -> Accu.t

  let map f x accu =
    x accu

  let pure _x accu =
    accu

  let apply f x accu =
    x (f accu)
end

module FoldT (Accu : TypeS) (Base : ApplicativeS)
  : ApplicativeS with type 'a t = Accu.t -> 'a Base.t * Accu.t = struct
  type 'a t = Accu.t -> 'a Base.t * Accu.t

  let map f x accu =
    let x, accu = x accu in
    (Base.map f x, accu)

  let pure x accu =
    Base.pure x, accu

  let apply f x accu =
    let f, accu = f accu in
    let x, accu = x accu in
    Base.apply f x, accu
end

module type VisitorS = sig
  module Applicative : ApplicativeS

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
            (visit_tuple a.tail tail) in

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
           (visit_record a.tail tail) in

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
        let module M = ListTraverse (V.Applicative) in
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
