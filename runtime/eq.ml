open Desc

open Tools

module Equaler = struct
  type ('a, 'b) t = 'a -> 'b -> bool
end

module Equalers = BinaryVector (Equaler)

type hook = {
    hook :
      'a 'b . 'a refl -> 'b refl -> ('a, 'b) Equaler.t -> ('a, 'b) Equaler.t
  }

let rec equal_poly :
  type a b structure arity_a arity_b rec_group positive negative direct gadt_a
    gadt_b .
  ?hook : hook ->
  (a, structure, arity_a, rec_group, [< Kinds.comparable],
    positive, negative, direct, gadt_a) desc ->
  (b, structure, arity_b, rec_group, [< Kinds.comparable],
    positive, negative, direct, gadt_b) desc ->
      (arity_a, arity_b, direct) Equalers.t ->
      (a, b) Equaler.t =
fun ?hook desc_a desc_b equalers ->
  let equal_tuple :
    type a b structure arity_a arity_b rec_group positive negative direct
      gadt_a gadt_b.
    (arity_a, arity_b, direct) Equalers.t ->
  (a, structure, arity_a, rec_group, [< Kinds.comparable],
    positive, negative, direct, gadt_a) Tuple.t ->
  (b, structure, arity_b, rec_group, [< Kinds.comparable],
    positive, negative, direct, gadt_b) Tuple.t ->
  bool =
  fun equalers x y ->
    let open Tuple.Items in
    match
      Tuple.find [x; y]
        begin fun (Tuple.Find { items = [x; y]; _ }) ->
          if equal_poly ?hook x.desc y.desc equalers x.value y.value then
            None
          else
            Some ()
        end
    with
    | None -> true
    | Some () -> false in
  let equal_record :
    type a b structure arity_a arity_b rec_group positive negative direct
      gadt_a gadt_b.
    (arity_a, arity_b, direct) Equalers.t ->
  (a, structure, arity_a, rec_group, [< Kinds.comparable],
    positive, negative, direct, gadt_a) Record.t ->
  (b, structure, arity_b, rec_group, [< Kinds.comparable],
    positive, negative, direct, gadt_b) Record.t ->
  bool =
  fun equalers x y ->
    let open Record.Fields in
    match
      Record.find [x; y]
        begin fun (Record.Find {items = [x; y]; _ }) ->
          match x.field, y.field with
          | Mono x', Mono y' ->
              if equal_poly ?hook x'.desc y'.desc equalers x.value y.value then
                None
              else
                Some ()
        end
    with
    | None -> true
    | Some () -> false in
  match desc_a, desc_b with
  | Variable index_a, Variable index_b ->
      Equalers.get index_a index_b equalers
  | Builtin Bool, Builtin Bool -> ( = )
  | Builtin Bytes, Builtin Bytes -> ( = )
  | Builtin Char, Builtin Char -> ( = )
  | Builtin Float, Builtin Float -> ( = )
  | Builtin Int, Builtin Int -> ( = )
  | Builtin Int32, Builtin Int32 -> ( = )
  | Builtin Int64, Builtin Int64 -> ( = )
  | Builtin Nativeint, Builtin Nativeint -> ( = )
  | Builtin String, Builtin String -> ( = )
  | Array desc_a, Array desc_b ->
      fun x y ->
      Array.length x = Array.length y &&
      let rec check i =
        i >= Array.length x ||
        equal_poly ?hook desc_a desc_b equalers
          (Array.unsafe_get x i) (Array.unsafe_get y i) &&
        check (succ i) in
      check 0
  | Constr a, Constr b ->
      fun x y ->
      let Constructor.Destruct x =
        Constructor.destruct a.constructors (a.destruct x) in
      let Constructor.Destruct y =
        Constructor.destruct b.constructors (b.destruct y) in
      begin match compare_binary_selection x.index_desc y.index_desc with
      | LessThan | GreaterThan -> false
      | Equal Eq ->
          let Eq =
            binary_selection_functional_head x.index_desc y.index_desc in
          match x.link, y.link with
          | Constructor.Exists xl, Constructor.Exists yl ->
              let Absent = xl.presence in
              let Eq =
                append_functional xl.variables.positive yl.variables.positive in
              let Eq =
                append_functional xl.variables.negative yl.variables.negative in
              let Eq =
                append_functional xl.variables.direct yl.variables.direct in
              let equalers =
                Equalers.append None xl.variables.presences
                  xl.variables.direct_count xl.variables.direct xl.exists_count
                  xl.exists yl.exists_count yl.exists equalers in
              begin match x.kind, y.kind with
              | Constructor.Tuple x, Constructor.Tuple y ->
                  equal_tuple equalers x y
              | Constructor.Record x, Constructor.Record y ->
                  equal_record equalers x y
              end
          | Constructor.Constructor, Constructor.Constructor ->
              match x.kind, y.kind with
              | Constructor.Tuple x, Constructor.Tuple y ->
                  equal_tuple equalers x y
              | Constructor.Record x, Constructor.Record y ->
                  equal_record equalers x y
      end
  | Object _, Object _ ->
      fun x y -> Oo.id x = Oo.id y
  | Tuple a, Tuple b ->
      fun x y ->
        equal_tuple equalers
          { structure = Tuple.of_desc a.structure; values = a.destruct x }
          { structure = Tuple.of_desc b.structure; values = b.destruct y }
  | Record a, Record b ->
      fun x y ->
        equal_record equalers
          { structure = a.structure; values = a.destruct x }
          { structure = b.structure; values = b.destruct y }
  | Variant a, Variant b ->
      fun x y ->
      let Variant.Destruct x = Variant.destruct a.constructors (a.destruct x) in
      let Variant.Destruct y = Variant.destruct b.constructors (b.destruct y) in
      begin match compare_selection x.index_desc y.index_desc with
      | LessThan | GreaterThan -> false
      | Equal Eq ->
          let Eq =
            selection_functional_head x.index_desc y.index_desc in
          match x.kind, y.kind with
          | Variant.Constructor { argument = Variant.None; _ },
            Variant.Constructor { argument = Variant.None; _ } -> true
          | Variant.Constructor { argument = Variant.Some x; _ },
            Variant.Constructor { argument = Variant.Some y; _ } ->
              equal_poly ?hook x.desc y.desc equalers x.value y.value
          | Variant.Inherit x, Variant.Inherit y ->
              equal_poly ?hook x.desc y.desc equalers x.value y.value
      end
  | Lazy desc_a, Lazy desc_b ->
      fun x y ->
        equal_poly ?hook desc_a desc_b equalers (Lazy.force x) (Lazy.force y)
  | Apply a, Apply b ->
      let equalers =
        Equalers.make
          { f = fun x -> equal_poly ?hook x } a.arguments b.arguments
          a.transfer equalers in
      equal_poly ?hook a.desc b.desc equalers
  | Rec a, Rec b ->
      let Eq = selection_functional_head a.index b.index in
      equal_poly ?hook a.desc b.desc equalers
  | RecGroup a, RecGroup b ->
      equal_poly ?hook a.desc b.desc equalers
  | Opaque _, Opaque _ ->
      fun _ _ -> true
  | MapOpaque, MapOpaque ->
      fun _ _ -> true
  | SelectGADT a, SelectGADT b ->
      equal_poly ?hook a.desc b.desc equalers
  | SubGADT a, SubGADT b ->
      equal_poly ?hook a.desc b.desc equalers
  | Attributes a, Attributes b ->
      equal_poly ?hook a.desc b.desc equalers
  | Name a, Name b ->
      begin match hook with
      | None -> equal_poly ?hook a.desc b.desc equalers
      | Some { hook = f } ->
          f a.refl b.refl (equal_poly ?hook a.desc b.desc equalers)
      end
  | _ -> .

let equal ?hook desc equalers =
  equal_poly ?hook desc desc equalers
