let () =
  let module IntNum : (Num with type t = int) = struct
      type t = int
      let one = 1
      let zero = 0
      let ( + ) = ( + )
      let ( * ) = ( * )
    end
  in
  let module D1 = AD (IntNum) in
  let module D2 = AD (D1)     in

  let x_cube'' = D1.diff (D2.diff D2.(fun x -> x * x * x)) in
  assert (x_cube'' 0 = 0);
  assert (x_cube'' 1 = 6);
  assert (x_cube'' 2 = 12);
  assert (x_cube'' 3 = 18);

  let dx, _ = D1.(grad (fun (x, z) ->
    let _, dy = D2.(grad (fun (x, y) -> x + y) (x, z)) in
    x * dy) (1, 1))
  in
  assert (dx = 1)
