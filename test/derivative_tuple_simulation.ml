open Ztypes

let runner ?(derivatives = [1.0; 2.0]) node =
  let size = List.length derivatives in
  let c = { dvec = Zls.cmake 0; cvec = Zls.cmake 0;
    zinvec = Zls.zmake 0; zoutvec = Zls.cmake 0;
    cindex = 0; zindex = 0; cend = 0; zend = 0;
    cmax = 0; zmax = 0; major = true; horizon = infinity } in
  let Node {alloc; reset; step} = node c in
  let mem = alloc () in
  c.cvec <- Zls.cmake c.cmax;
  c.dvec <- Zls.cmake c.cmax;
  c.zinvec <- Zls.zmake c.zmax;
  c.zoutvec <- Zls.cmake c.zmax;
  assert (c.cmax = size);
  reset mem;
  let call major t =
    c.major <- major; c.cindex <- 0; c.zindex <- 0;
    step mem (t, ()) in
  ignore (call true 0.0);
  fun i ->
    for j = 0 to c.zmax - 1 do
      Zls.set c.zinvec j (if i = 10 || i = 20 then 1l else 0l)
    done;
    ignore (call false (float i *. 0.1));
    let rates = List.init size (Zls.get c.dvec) in
    let actual = List.sort compare rates in
    assert (actual = derivatives);
    let output = call true (float i *. 0.1) in
    for j = 0 to size - 1 do
      Zls.set c.cvec j (Zls.get c.cvec j +. 0.1 *. List.nth rates j)
    done;
    output

let () =
  let tuple = runner Derivative_tuple.tuple in
  let scalar = runner Derivative_tuple.scalar in
  let named = runner Derivative_tuple.named in
  let nested = runner ~derivatives:[1.0; 2.0; 3.0] Derivative_tuple.nested in
  let computed = runner ~derivatives:[0.0; 1.0] Derivative_tuple.computed in
  for i = 0 to 30 do
    let a = tuple i and b = scalar i in
    assert (a = b);
    assert (named i = a);
    let x, y, _ = nested i in
    assert ((x, y) = a);
    let x, y = computed i in
    assert (x = 0.0 && abs_float (y -. float i *. 0.1) < 1e-10);
    if i = 0 || i = 10 || i = 20 then assert (a = (0.0, 0.0))
  done;
  print_endline "Tuple and scalar simulation agree for 31 steps, including two resets."
