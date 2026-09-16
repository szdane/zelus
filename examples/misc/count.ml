(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type ('b , 'a) _count =
  { mutable i_23 : 'b ; mutable m_20 : 'a }

let count  = 
   let count_alloc _ =
     ();{ i_23 = (false:bool) ; m_20 = (42:int) } in
  let count_reset self  =
    (self.i_23 <- true:unit) in 
  let count_step self (x_18:int) =
    ((let (next_21:int) = self.m_20 in
      let (next_22:int) = if self.i_23 then x_18 else (+) next_21  x_18 in
      self.i_23 <- false ;
      (let (o_19:int) = next_22 in
       self.m_20 <- o_19 ; o_19)):int) in
  Node { alloc = count_alloc; reset = count_reset ; step = count_step }
type ('a) _main =
  { mutable i_26 : 'a }

let main  = 
  let Node { alloc = i_26_alloc; step = i_26_step ; reset = i_26_reset } = count 
   in let main_alloc _ =
        ();{ i_26 = i_26_alloc () (* discrete *)  } in
  let main_reset self  =
    (i_26_reset self.i_26 :unit) in 
  let main_step self () =
    ((let (x_24:int) = read_int () in
      let (y_25:int) = i_26_step self.i_26 x_24 in
      let _ = print_int y_25 in
      print_newline ()):unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
