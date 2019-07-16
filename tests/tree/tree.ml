type 'a t =
  | Leaf
  | Node of { left : 'a t; label : 'a; right : 'a t }
        [@@deriving refl]

let () =
  assert (Refl.map [%refl: _ t] [%refl: _ t] [P string_of_int]
    (Node {
      left = Node {
        left = Leaf;
        label = 1;
        right = Node { left = Leaf; label = 2; right = Leaf }};
      label = 3;
      right = Leaf }) =
    (Node {
      left = Node {
        left = Leaf;
        label = "1";
        right = Node { left = Leaf; label = "2"; right = Leaf }};
      label = "3";
      right = Leaf }));
  assert (Refl.compare [%refl: _ t] [Some Int.compare]
    (Node {
      left = Node {
        left = Leaf;
        label = 1;
        right = Node { left = Leaf; label = 4; right = Leaf }};
      label = 3;
      right = Leaf })
    (Node {
      left = Node {
        left = Leaf;
        label = 1;
        right = Node { left = Leaf; label = 2; right = Leaf }};
      label = 3;
      right = Leaf }) = 1)
