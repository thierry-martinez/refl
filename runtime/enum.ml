open Desc

open Tools

type ('a, 'arity, 'b) typed_attribute_kind +=
  | Attribute_value : ('a, 'arity, int) typed_attribute_kind

let rec lift_zero (l : ('cases binary_choice * int option) list) :
    (('cases * _) binary_choice * int option) list =
  match l with
  | [] -> []
  | (choice, value) :: tl -> (CZero choice, value) :: lift_zero tl

let rec lift_one (l : ('cases binary_choice * int option) list) :
    ((_ * 'cases) binary_choice * int option) list =
  match l with
  | [] -> []
  | (choice, value) :: tl -> (COne choice, value) :: lift_one tl

let rec merge l0 l1 =
  match l0, l1 with
  | hd0 :: tl0, hd1 :: tl1 -> hd0 :: hd1 :: merge tl0 tl1
  | _, [] -> l0
  | [], l1 -> l1

let rec constructor_assoc :
  type cases structures .
  (cases, structures, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructors ->
  (cases binary_choice * int option) list =
fun constructors ->
  match constructors with
  | CNode { zero; one } ->
      merge
        (lift_zero (constructor_assoc zero))
        (lift_one (constructor_assoc one))
  | CLeaf constructor ->
      begin match constructor with
      | Constructor { kind = CTuple TNil; eqs = ENil; attributes; _ } ->
          [(CEnd ((), ()), attributes.typed Attribute_value)]
      | _ -> []
      end

let constructor_assoc_with_default_values constructors =
  let assoc = constructor_assoc constructors in
  let put_default_value (default, accu) (choice, value) =
    let value = Stdcompat.Option.value ~default value in
    (succ value, (choice, value) :: accu) in
  let (_default_value, accu) =
    List.fold_left put_default_value (0, []) assoc in
  List.rev accu

let fold :
  type a .
  (int -> int -> int) ->
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int =
fun op constructors ->
  match constructors with
  | Name { desc = RecArity { desc = Constr { constructors; _ }; _}; _ } ->
      match constructor_assoc_with_default_values constructors with
      | [] -> 0
      | (_, value) :: tail ->
          List.fold_left (fun a (_, b) -> op a b) value tail

let min :
  type a .
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int =
fun constructors ->
  fold min constructors

let max :
  type a .
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int =
fun constructors ->
  fold max constructors

let check_choice (c : 'cases binary_choice)
    ((c', _) : ('cases binary_choice * int)) =
  Tools.equal_binary_choice c c'

let check_value (v : int)
    ((_, v') : ('cases binary_choice * int)) =
  v = v'

let to_int_opt :
  type a .
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  a -> int option =
fun desc value ->
  match desc with
  | Name { desc = RecArity { desc =
      Constr { constructors; destruct; _ }; _ }; _ } ->
      Stdcompat.Option.map snd
        (Stdcompat.List.find_opt (check_choice (destruct value))
          (constructor_assoc_with_default_values constructors))

let of_int_opt :
  type a .
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  int -> a option =
fun desc value ->
  match desc with
  | Name { desc = RecArity { desc =
      Constr { construct; constructors; _ }; _ }; _ } ->
      Stdcompat.Option.map (fun item -> construct (fst item))
        (Stdcompat.List.find_opt (check_value value)
           (constructor_assoc_with_default_values constructors))

let to_string :
  type a .
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  a -> string =
fun desc value ->
  match desc with
  | Name { desc = RecArity { desc =
      Constr { constructors; destruct; _ }; _ }; _ } ->
      let Constructor.Destruct destruct =
        Constructor.destruct constructors (destruct value) in
      destruct.name

let rec of_string_aux :
  type cases structures .
  (cases, structures, 'arity, 'rec_arity, 'kinds, 'positive,
    'negative, 'direct, 'gadt) constructors ->
  string ->
  cases binary_choice option =
fun constructors value ->
  match constructors with
  | CNode { zero; one } ->
      begin match of_string_aux zero value with
      | None -> Stdcompat.Option.map (fun c -> COne c) (of_string_aux one value)
      | some -> Stdcompat.Option.map (fun c -> CZero c) some
      end
  | CLeaf (Constructor c) when c.name = value ->
      begin match c.kind, c.eqs with
      | CTuple TNil, ENil ->
          Some (CEnd ((), ()))
      | _ -> None
      end
  | _ -> None

let of_string_opt :
  type a .
  (a, [`Name of [`RecArity of [`Constr of 'structures] * _]],
    'arity, 'rec_arity, 'kinds, 'positive, 'negative, 'direct, 'gadt) desc ->
  string -> a option =
fun desc value ->
  match desc with
  | Name { desc = RecArity { desc =
      Constr { construct; constructors; _ }; _ }; _ } ->
      match of_string_aux constructors value with
      | None -> None
      | Some choice -> Some (construct choice)
