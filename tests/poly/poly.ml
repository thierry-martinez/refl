type 'a t = {
    f : 'b . 'a -> 'b -> 'a * 'b
  }

type ('present, 'unknown) t__variable_positive0 = 'present
type ('present, 'unknown) t__variable_negative0 = 'present
type ('present, 'unknown) t__variable_direct0 = 'unknown
type t__arity = [`Succ of [`Zero]]
type t__sub_structure =[
         `Arrow of
           [ `Variable of [`Succ of [`Zero]] ] ->
             [
               `Arrow of
                 [ `Variable of [`Zero]] ->
                   [
                     `Tuple of
                       ([ `Variable of [`Succ of [`Zero]]] *
                         ([ `Variable of [`Zero]] *
                         unit))
                       ]
                 ]]
type t__structure =
  [`Record of
      ([`Poly of t__sub_structure * [`Succ of [`Zero]] * ([`Present] * unit)
        * ([`Present] * unit) * ([`Absent] * unit)] * unit)]
type t__rec_arity = ((t__arity * t__structure) * unit)
type t__kinds = [ `Variable  | `Tuple  | `Record  | `Arrow | `Poly ]
let t__variable_positive0 refl__present refl__absent = refl__present
and t__variable_positive1 refl__present refl__absent = refl__present
and t__variable_negative0 refl__present refl__absent = refl__present
and t__variable_negative1 refl__present refl__absent = refl__present
and t__variable_direct0 refl__present refl__absent = refl__absent
and t__variable_direct1 refl__present refl__absent = refl__absent
let _ = t__variable_positive0
and _ = t__variable_positive1
and _ = t__variable_negative0
and _ = t__variable_negative1
and _ = t__variable_direct0
and _ = t__variable_direct1
let t_refl : type a0 .
    (a0 t, t__structure, (a0 * unit), t__rec_arity,
      [> t__kinds],
      (([ `Present ], [ `Absent ]) t__variable_positive0 * unit),
      (([ `Present ], [ `Absent ]) t__variable_negative0 * unit),
      (([ `Present ], [ `Absent ]) t__variable_direct0 * unit), unit)
      Refl.desc
  =
  let substructure =Refl.Arrow
                      {
                        parameter = (Refl.Variable (Refl.VNext Refl.VFirst));
                        result =
                          (Refl.Arrow
                             {
                               parameter =
                                 (Refl.Variable Refl.VFirst);
                               result =
                                 (Refl.Tuple
                                    {
                                      structure =
                                        (Refl.TCons
                                           {
                                             head = Refl.Variable (Refl.VNext Refl.VFirst);
                                             tail =
                                               (Refl.TCons
                                                  {
                                                    head = Refl.Variable Refl.VFirst;
                                                    tail = Refl.TNil
                                                  })
                                           });
                                      construct =
                                        (function
                                         | (item0, (item1, ())) -> (item0, item1)
                                         | _ -> .);
                                      destruct =
                                        (function
                                         | (item0, item1) -> (item0, (item1, ())))
                                    })
                             })
                     } in
  Refl.Record
    {
      structure =
        RCons {
          head =
            begin
              let forall_destruct : type forall subarity .
                ([`Succ of [`Zero]], forall) Refl.length ->
                (forall, a0 * unit, subarity) Refl.append ->
                (a0 t, t__sub_structure, subarity, t__rec_arity, t__kinds,
                 [`Present] * ([`Present] * unit),
                 [`Present] * ([`Present] * unit),
                 [`Absent] * ([`Absent] * unit), unit)
                   Refl.forall_destruct_result =
              fun count arity ->
                let Succ Zero = count in
                let Add Nil = arity in
                ForallDestruct {
                  desc = substructure;
                  destruct = fun { f } -> f;
                } in
              Refl.Poly {
                label = "f";
                variables = {
                  presences = AddAbsent Presences;
                  positive_count = Succ Zero;
                  positive = Add Nil;
                  negative_count = Succ Zero;
                  negative = Add Nil;
                  direct_count = Succ Zero;
                  direct = Add Nil;
                };
                destruct = { forall_destruct };
                construct = fun { forall_construct } ->
                  { f =
                      fun x ->
                        forall_construct (Succ Zero) (Add Nil) substructure x };
              };
            end;
          tail = RNil };
      construct =
        (function
         | ({ f }, ()) -> { f });
      destruct =
        (function
         | { f } -> ({ f }, ()))
    }
let _ = t_refl

type 'a u = {
    f : 'b . 'a -> 'b -> 'a * 'b
  }
      [@@deriving refl]

let () =
  let u = { f = fun x y -> (succ x, y) } in
  let u' =
    Refl.map [%refl: _ u] [%refl: _ u] [PN (string_of_int, int_of_string)] u in
  assert (u'.f "1" true = ("2", true));
  assert (u'.f "3" 2.5 = ("4", 2.5));
  assert (Refl.show [%refl: _ u] [None] u' = "{ f = <fun> }")

type 'a v =
  | A of {
      a : float;
      f : 'b . 'a -> 'b -> 'a * 'b;
    }
  | B of {
      x : int;
      f : 'b . 'a -> 'b -> 'a * 'b;
      g : 'b . bool -> 'b -> 'b -> 'b;
    }
      [@@deriving refl]
