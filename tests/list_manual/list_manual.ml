type structure =
  [`Constr of ([`Constructor of [`Tuple of unit] * unit]) *
    (([`Constructor of ([`Tuple of [`Variable of [`Zero]] *
      ([`Rec of [`Zero]] * unit)]) * unit]) *
    unit)]

type arity = [`Succ of [`Zero]]

type rec_arity = (arity * structure) * unit

type index = [`Succ of [`Zero]]

type kinds = [`Constr]

let index : (index, rec_arity, arity * structure, unit) Refl.selection = Next Start

let rec list_refl : ('a list, structure, 'arity, rec_arity, [> kinds],
  [> `Present] * unit, [> `Absent] * unit, [> `Present] * unit, unit)
    Refl.desc =
  Constr {
    constructors =
      CCons {
        head = Constructor {
          name = "nil";
          kind = CTuple TNil;
          eqs = ENil;
          attributes = Refl.Tools.attributes_empty; };
      tail = CCons {
        head = Constructor {
          name = "cons";
          kind = CTuple (TCons {
              head = Variable VFirst;
            tail = TCons {
              head = Rec {
                   index = index;
                   desc = list_refl;
                       };
            tail = TNil }});
          eqs = ENil;
          attributes = Refl.Tools.attributes_empty; };
      tail = CNil }};
    construct = begin fun x ->
      match x with
      | CFirst _ -> []
      | CNext (CFirst ((hd, (tl, ())), ())) ->
          hd :: tl
      | _ -> .
    end;
    destruct = begin fun x ->
      match x with
      | [] -> CFirst ((), ())
      | hd :: tl ->
          CNext (CFirst ((hd, (tl, ())), ()))
    end;
  }

let () =
  assert
    (Refl.map list_refl list_refl [P string_of_int] [1; 2; 3] = ["1"; "2"; "3"])
