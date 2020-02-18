(*
type 'a t =
  | [] : [`Zero] t

type ('present, 'unknown) t__variable_positive0 = 'present
type ('present, 'unknown) t__variable_negative0 = 'unknown
type ('present, 'unknown) t__variable_direct0 = 'present
type t__arity = [`Succ of [`Zero]]
type t__structure = [ `Constr of ([`Constructor of [ `Tuple of unit ] * ([`Zero] * unit)] * unit) ]
type t__rec_arity = ((t__arity * t__structure) * unit)
type t__kinds = [ `Constr | `GADT ]
let t__variable_positive0 refl__present refl__absent = refl__present
and t__variable_negative0 refl__present refl__absent = refl__absent
and t__variable_direct0 refl__present refl__absent = refl__present
let _ = t__variable_positive0
and _ = t__variable_negative0
and _ = t__variable_direct0
let t_refl :
  'a0 .
    ('a0 t, t__structure, ('a0 * unit), t__rec_arity, [> t__kinds],
      (([ `Present ], [ `Absent ]) t__variable_positive0 * unit),
      (([ `Present ], [ `Absent ]) t__variable_negative0 * unit),
      (([ `Present ], [ `Absent ]) t__variable_direct0 * unit), (('a0, [`Zero]) Refl.eq * unit)) Refl.desc
  =
  let construct :
    type a . ((unit * ((a, [`Zero]) Refl.eq * unit)) * unit) Refl.choice -> a t =
    function | Refl.CFirst ((), (Refl.Eq, ())) -> [] | _ -> . in
  let destruct :
    type a . a t -> ((unit * ((a, [`Zero]) Refl.eq * unit)) * unit) Refl.choice =
    function | [] -> Refl.CFirst ((), (Refl.Eq, ())) in
  Refl.Constr
    {
      constructors =
        (Refl.CCons {
          head =
            Constructor {
              name = "[]";
              kind = (Refl.CTuple Refl.TNil);
              eqs = Refl.ECons {
                head = Next Start;
                tail = Refl.ENil };
              attributes = Refl.Tools.attributes_empty;
            };
          tail = Refl.CNil });
      construct;
      destruct;
    }
let _ = t_refl
*)

type ('a, 'b) u =
  | [] : ([`Zero], 'b) u
  | (::) : 'b * 'b -> ([`Succ], 'b) u
      [@@deriving refl]

let () =
  assert (Refl.show [%refl: (_, int) u] [None] [] = "[]")

let () =
  assert (Refl.show [%refl: (_, int) u] [None] (1 :: 2) = "1 :: 2")

let () =
  let refl = [%refl: ('a, 'b) u] in
  assert (Refl.map refl refl
    [None; P string_of_int] (1 :: 2) = ("1" :: "2"))

type ('a, 'b, 'c) labeled_eq =
  | LabeledEq : 'c -> ('a, 'a, 'c) labeled_eq
      [@@deriving refl]

let () =
  assert (Refl.show [%refl: ('a, 'a, 'b) labeled_eq]
    [None; Some (Format.pp_print_int)] (LabeledEq 1) = "LabeledEq (1)")

let () =
  let refl = [%refl: ('a, 'a, 'b) labeled_eq] in
  assert (Refl.map refl refl
    [None; P string_of_int] (LabeledEq 1) = LabeledEq "1")

type 'a v =
  | A : 'a * 'b -> ('a * 'b) v

(*
type ('present, 'unknown) v__variable_positive0 = 'present
type ('present, 'unknown) v__variable_negative0 = 'unknown
type ('present, 'unknown) v__variable_direct0 = 'present
type v__arity = [`Succ of [`Zero]]
type v__structure_sub = [`Tuple of [`Variable of [`Zero]] * ([`Variable of [`Succ of [`Zero]]] * unit)]
type v__structure = [ `Constr of (
  [`Exists of [`Zero] * [`Succ of [`Succ of [`Zero]]] * v__structure_sub * [`Present] *
  ([`Present] * ([`Present] * unit)) * ([`Absent] * ([`Absent] * unit))
  * ([`Present] * ([`Present] * unit))]) * unit ]
type v__rec_arity = ((t__arity * t__structure) * unit)
type v__kinds = [ `Variable | `Tuple | `Constr | `GADT | `Exists | `Present]
let v__variable_positive0 refl__present refl__absent = refl__present
and v__variable_negative0 refl__present refl__absent = refl__absent
and v__variable_direct0 refl__present refl__absent = refl__present

type 'a v__gadt = 'a * unit

type ('constraints, 'exists) Refl.gadt_constraints +=
  | GADT_V : ('a * 'b, 'a * ('b * unit)) Refl.gadt_constraints

type v__exists_count = [`Succ of [`Succ of [`Zero]]]

let v_refl :
  type a0 .
    (a0 v, v__structure, (a0 * unit), v__rec_arity, [> v__kinds],
      (([ `Present ], [ `Absent ]) v__variable_positive0 * unit),
      (([ `Present ], [ `Absent ]) v__variable_negative0 * unit),
      (([ `Present ], [ `Absent ]) v__variable_direct0 * unit), a0 v__gadt)
        Refl.desc
  =
  let construct :
      (a0 v * unit) Refl.choice -> a0 v = function
    | Refl.CFirst x ->
          x
    | _ -> . in
  let destruct : a0 v ->
      (a0 v * unit) Refl.choice = function
    | A (x, y) ->
        Refl.CFirst (A (x, y)) in
  Refl.Constr
    {
      constructors =
        (Refl.CCons {
          head =
begin
    let kind =
              Refl.CTuple (Refl.TCons {
                head = Refl.Variable VFirst;
                tail = TCons {
                  head = Refl.Variable (VNext VFirst);
                  tail = TNil }}) in
    let construct :
      type exists arity subarity .
      (v__exists_count, exists) Refl.length ->
      (a0, exists) Refl.gadt_constraints ->
      (exists, arity, subarity) Refl.append ->
      (a0 v, v__structure_sub, subarity, v__rec_arity, v__kinds,
        [`Present] * ([`Present] * ([`Present] * unit)),
        [`Absent] * ([`Absent] * ([`Absent] * unit)),
        [`Present] * ([`Present] * ([`Present] * unit)),
        a0 v__gadt) Refl.exists_construct =
    fun exists_count constraints exists ->
      let Succ (Succ Zero), Add (Add Nil) = exists_count, exists in
      match constraints with
      | GADT_V ->
          Refl.ExistsConstruct {
            kind;
            construct = (fun (x, (y, ())) -> A (x, y));
          }
      | _ -> assert false in
    let destruct : type a0 . a0 v ->
      ([`Succ of [`Succ of [`Zero]]], a0,
        a0 v, v__structure_sub, a0 * unit, v__rec_arity, v__kinds,
        [`Present] * ([`Present] * ([`Present] * unit)),
        [`Absent] * ([`Absent] * ([`Absent] * unit)),
        [`Present] * ([`Present] * ([`Present] * unit)),
        a0 v__gadt) Refl.exists_destruct=
    fun (type a0) (value : a0 v) :
      ([`Succ of [`Succ of [`Zero]]], a0,
        a0 v, v__structure_sub, a0 * unit, v__rec_arity, v__kinds,
        [`Present] * ([`Present] * ([`Present] * unit)),
        [`Absent] * ([`Absent] * ([`Absent] * unit)),
        [`Present] * ([`Present] * ([`Present] * unit)),
        a0 v__gadt) Refl.exists_destruct ->
      let A (x, y) = value in
      Refl.ExistsDestruct {
        exists_count = Succ (Succ Zero);
        exists = Add (Add Nil);
        constraints = GADT_V;
        kind;
        values = (x, (y, ()));
      } in
            Refl.Exists {
              presence = Present;
              variables = {
                presences = AddPresent (AddPresent Presences);
                positive_count = Succ (Succ Zero);
                negative_count = Succ (Succ Zero);
                direct_count = Succ (Succ Zero);
                positive = Add (Add Nil);
                negative = Add (Add Nil);
                direct = Add (Add Nil);
              };
              name = "A";
              selection = Next Start;
              construct;
              destruct;
            }
end;
          tail = Refl.CNil });
      construct;
      destruct;
    }
*)
type 'a w =
  | A : 'a * 'b -> ('a * 'b) w
        [@@deriving refl]

type ('a, 'b) vector =
  | [] : ('a, [`Zero]) vector
  | (::) : 'a * ('a, 'b) vector -> ('a, [`Succ of 'b]) vector
        [@@deriving refl]

let () =
  assert
    (Refl.map [%refl: (_, _) vector] [%refl: (_, _) vector]
       [P string_of_int; None] [1; 2; 3] = ["1"; "2"; "3"])

let () =
  assert
    (Refl.compare_poly [%refl: (_, _) vector] [%refl: (_, _) vector]
       [Some Int.compare; None] [1; 2] [1; 2; 3] < 0)

let () =
  assert
    (Refl.compare_poly [%refl: (_, _) vector] [%refl: (_, _) vector]
       [Some Int.compare; None] [1; 2; 3] [1; 2] > 0)

let () =
  assert
    (Refl.compare vector_refl
       [Some Int.compare; None] [1; 2; 3] [1; 2; 3] = 0)

let () =
  assert (Refl.show [%refl: (int, _) vector] [None] [1; 2; 3] = "[1; 2; 3]")

type poly = Poly : 'a -> poly
    [@@deriving refl]

let () =
  assert (Refl.show [%refl: poly] [] (Poly 0) = "Poly (<poly>)")

(*
let () =
  assert
    (Refl.compare [%refl:poly] (Poly 0) (Poly 1) = 0)
*)
