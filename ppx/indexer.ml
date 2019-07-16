module Make (T : Map.OrderedType) = struct
  module Map = Map.Make (T)

  type t = {
      count : int;
      map : int Map.t;
    }

  let of_fresh count = { count; map = Map.empty }

  let empty = of_fresh 0

  let count indexer = indexer.count

  let to_map indexer = indexer.map

  let fresh indexer =
    let index = indexer.count in
    index, { indexer with count = succ indexer.count }

  let force_add item indexer =
    let index, indexer = fresh indexer in
    index, { indexer with map = Map.add item index indexer.map }

  let mem item indexer =
    Map.mem item indexer.map

  let find item indexer =
    Map.find item indexer.map

  let find_opt item indexer =
    Map.find_opt item indexer.map

  let add item indexer =
    try find item indexer, indexer
    with Not_found -> force_add item indexer

  let of_list list =
    List.fold_left begin fun indexer x ->
      snd begin match x with
      | None -> fresh indexer
      | Some x -> force_add x indexer
      end
    end empty list

  let union indexer indexer' = {
    count = indexer.count + indexer'.count;
    map =
      Map.map (fun index -> index + indexer.count) indexer'.map |>
      Map.union (fun _ _ _ -> invalid_arg "Indexer.union") indexer.map
  }
end
