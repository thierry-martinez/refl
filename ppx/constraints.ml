open Common

module type PropertyWithLub = sig
  include Fix.PROPERTY

  type t = property

  val union : property -> property -> property
end

module Transfer = struct
  type t =
    | Present
    | Absent
    | Constr of Longident.t * t * t

  let rec compose t t' =
    match t, t' with
    | Present, _ | _, Present -> Present
    | Absent, _ -> t'
    | _, Absent -> t
    | Constr (c, present, absent), _ ->
        Constr (c, present, compose absent t')

  let compare = Stdlib.compare

  let rec to_type t =
    let loc = !Ast_helper.default_loc in
    match t with
    | Present -> [%type: [`Present]]
    | Absent -> [%type: [`Absent]]
    | Constr (txt, present, absent) ->
        Ast_helper.Typ.constr { loc; txt } [to_type present; to_type absent]
end

module PropertyOfSet (X : Set.S)
    : PropertyWithLub with type property = X.t = struct
  type t = X.t

  type property = X.t

  let bottom = X.empty

  let equal = X.equal

  let union = X.union

  let is_maximal _ = false
end

let compare_pair compare_x compare_y (x, y) (x', y') =
  match compare_x x x' with
  | 0 -> compare_y y y'
  | result -> result

module PairOfOrderedType (X : Set.OrderedType) (Y : Set.OrderedType)
  : Set.OrderedType with type t = X.t * Y.t = struct
  type t = X.t * Y.t

  let compare = compare_pair X.compare Y.compare
end

module PropertyOfPair (X : PropertyWithLub) (Y : PropertyWithLub)
    : PropertyWithLub with type property = X.t * Y.t = struct
  type t = X.t * Y.t

  type property = t

  let bottom = (X.bottom, Y.bottom)

  let equal (x, y) (x', y') =
    X.equal x x' && Y.equal y y'

  let union (x, y) (x', y') =
    (X.union x x', Y.union y y')

  let is_maximal (x, y) = X.is_maximal x && Y.is_maximal y
end

let rec compare_list compare_item l l' =
  match l, l' with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | hd :: tl, hd' :: tl' ->
      compare_pair compare_item (compare_list compare_item) (hd, tl) (hd', tl')

module TransferSet = Set.Make (Transfer)

module Kinds = struct
  include PropertyOfPair (PropertyOfSet (TransferSet)) (PropertyOfPair
      (PropertyOfSet (StringSet))
      (PropertyOfSet (LongidentSet)))

  let to_type (exists, (direct, inherited)) =
    let row_fields =
      if TransferSet.is_empty exists then
        []
      else
        [Metapp.Rf.inherit_
          (Transfer.to_type
            (TransferSet.fold Transfer.compose exists Absent))] in
    let add_direct_kind txt accu =
      Metapp.Rf.tag (Metapp.mkloc txt) false [] :: accu in
    let row_fields = StringSet.fold add_direct_kind direct row_fields in
    let add_inherited_kind txt accu =
      Metapp.Rf.inherit_
        (Ast_helper.Typ.constr (Metapp.mkloc txt) []) :: accu in
    let row_fields =
      LongidentSet.fold add_inherited_kind inherited row_fields in
    let row_fields =
      if row_fields = [] then
        [Metapp.Rf.tag (Metapp.mkloc "Absent") false []]
      else
        row_fields in
    Ast_helper.Typ.variant row_fields Closed None
end


module Variables = struct
  module Path = struct
    module PathItem = PairOfOrderedType (OrderedLongident) (Int)

    type t = origin * selector
    and selector =
      | Left
      | Right
      | Direct
    and origin = PathItem.t list

    let left selector =
      match selector with
      | Direct
      | Right -> Left
      | Left -> Right

    let right selector =
      match selector with
      | Direct
      | Right -> Right
      | Left -> Left

    let compare : t -> t -> int =
      compare_pair (compare_list PathItem.compare) compare
  end

  module PathSet = Set.Make (Path)

  type t = PathSet.t IntMap.t

  let find i variables =
    try IntMap.find i variables
    with Not_found -> PathSet.empty

  let add i path variables =
    let path_set = PathSet.add path (find i variables) in
    IntMap.add i path_set variables

  let offset count variables =
    IntMap.fold (fun key value map ->
      if key >= count then
        IntMap.add (key - count) value map
      else
        map) variables IntMap.empty

  type property = t

  let bottom = IntMap.empty

  let equal =
    IntMap.equal PathSet.equal

  let union =
    IntMap.union (fun _ p p' -> Some (PathSet.union p p'))

  let is_maximal _ = false

  let variable_name side type_name i =
     type_name ^ "__variable_" ^ side ^ (string_of_int i)

  let positive_name = variable_name "positive"

  let negative_name = variable_name "negative"

  let direct_name = variable_name "direct"

  let gadt_name = variable_name "gadt"

  type transfer =
    | Present
    | Depend of Longident.t list list

  let make_transfer variables target i =
    let paths = find i variables in
    if PathSet.mem ([], target) paths
        || target = Right && PathSet.mem ([], Direct) paths then
      Present
    else
      let rec add_path (selector : Path.selector) path t cstrs =
        match path with
        | [] ->
            begin match target, selector with
            | Left, Left
            | Right, (Direct | Right)
            | Direct, Direct -> t :: cstrs
            | _ -> cstrs
            end
        | (longident, i) :: path ->
            let apply subst =
              subst_ident (fun name -> subst name i) longident :: t in
            if target = Direct then
              add_path selector path (apply direct_name) cstrs
            else
              cstrs |>
              add_path (Path.left selector) path (apply negative_name) |>
              add_path (Path.right selector) path (apply positive_name) in
      let add_inherited (origin, selector) cstrs =
        add_path selector origin [] cstrs in
      Depend (PathSet.fold add_inherited paths [])

  type transfers = (Longident.t * transfer) list

  let make_transfers type_name arity variables =
    let make target name i =
      name type_name i, make_transfer variables target i in
    List.init arity (make Right positive_name) @
    List.init arity (make Left negative_name) @
    List.init arity (make Direct direct_name)
end

include PropertyOfPair (Kinds) (Variables)

let add_direct_kind kind ((exists, (direct, inherited)), variables) =
  ((exists, (StringSet.add kind direct, inherited)), variables)

let add_inherited_kind type_name ((exists, (direct, inherited)), variables) =
  ((exists, (direct, LongidentSet.add type_name inherited)), variables)

let add_exists_kind transfer ((exists, others), variables) =
  ((TransferSet.add transfer exists, others), variables)

let add_variable variable path ((kinds, variables) : t) =
  (kinds, Variables.add variable path variables)

let offset_variables count ((kinds, variables) : t) =
  (kinds, Variables.offset count variables)
