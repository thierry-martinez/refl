# Efficient and type-safe type reflection for OCaml

`refl` provides runtime representations for most OCaml types, and a
"one size fits all" deriving plugin.
This plugin automatically derives runtime type
representations from type declarations, allowing most other deriving
plugins to be rewritten as regular OCaml functions parametized by
these runtime representations.
The library also provides such functions which provides flexible
alternatives to `ppx_deriving` standard plugins: `show`, `compare`,
`eq`, `map`, `iter`, `fold`, `enum`, `make`.

Once `refl` is derived for a given type, values of this type can be
used on all (compatible) functions. This is the main motivation behind
`refl`: instead of having to decide which derivers to use at the
type declaration point, it is sufficient to derive only `refl`, and
then this type can be used with all functions operating on such
runtime representations, even functions that are defined after the
type declaration.

# Basic usage

The following example declares a type for binary trees along with its
runtime representation.

```ocaml
type 'a binary_tree =
  | Leaf
  | Node of { left : 'a binary_tree; label : 'a; right : 'a binary_tree }
        [@@deriving refl]
```

The function `Refl.show` can be used to print such trees, the function
`Refl.compare` can be used to compare two binary trees, the function
`Refl.map` can be used to change labels, etc. For instance:

```ocaml
# Refl.show [%refl: string binary_tree] []
    (Node { left = Leaf; label = "root"; right = Leaf });;
- : string = "Node { left = Leaf; label = \"root\"; right = Leaf }"
```

Built-in types can be used directly without prior declaration.

```ocaml
# Refl.show [%refl: (string * int) list] [] ["a", 1; "b", 2];;
- : string = "[(\"a\", 1); (\"b\", 2)]"
```

When a type contains type variables, custom printers for these
variables should be listed in the second argument of `Refl.show`.

```ocaml
# Refl.show [%refl: _ list] [Some Format.pp_print_string] ["a"; "b"; "c"];;
- : string = "[a; b; c]"
```

The custom printers are optional for skipping "shadow" type variables,
that is to say type variables that are not used to type
sub-values. This will be particularly useful for GADTs.
Typically, shadow type variables appear in GADTs as
indexes. For instance, consider the following definition for
fixed-length vector.

```ocaml
type ('a, 'length) vector =
  | [] : ('a, [`Zero]) vector
  | (::) : 'a * ('a, 'length) vector -> ('a, [`Succ of 'length]) vector
        [@@deriving refl]
```

When applying `Refl.show` to vectors, `None` can be passed for the printer
of the second parameter (`'length`), since it will never be used.

```ocaml
# Refl.show [%refl: (_, _) vector] [Some Format.pp_print_string; None]
    ["a"; "b"; "c"];;
- : string = "[a; b; c]"
```

Another example of function is `Refl.map`, that applies a given
function for each type variables.

```ocaml
# Refl.map [%refl: _ binary_tree] [%refl: _ binary_tree] [P string_of_int]
    (Node { left = Leaf; label = 1; right = Leaf });;
  - : string binary_tree = Node {left = Leaf; label = "1"; right = Leaf}
```

Note that the reflexive representation keeps track whether type variables
occur positively or negatively.
The `P` constructor above marks functions appliable to type variables that
appear positively (outside arrow types or at the right-hand side of arrow types).
For types that appear negatively, functions in the reverse direction should be
provided, marked with `N`.
For types that appear both positively and negatively, a pair of functions for
both directions should be provided, marked with `PN`.

# Type constraints

Functions can require constraints to be satisfied by the type to be
applicable: for instance, the function `compare` requires that the
type contains no arrows unless they are hidden by an `[@opaque]`
attribute.
