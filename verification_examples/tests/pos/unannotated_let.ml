(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
let theta = 1.

type _noise = unit

let noise  = 
   let noise_alloc _ = () in
  let noise_reset self  =
    ((()):unit) in 
  let noise_step self () =
    ((let (n_49:float) = theta in
      n_49):float) in
  Node { alloc = noise_alloc; reset = noise_reset ; step = noise_step }
type _shift = unit

let shift  = 
   let shift_alloc _ = () in
  let shift_reset self  =
    ((()):unit) in 
  let shift_step self ((x_50:int): int) =
    ((let (y_51:int) = (+) x_50  7 in
      y_51):int) in
  Node { alloc = shift_alloc; reset = shift_reset ; step = shift_step }
type _inc = unit

let inc  = 
   let inc_alloc _ = () in
  let inc_reset self  =
    ((()):unit) in 
  let inc_step self ((a_52:int): int) =
    ((+) a_52  1:int) in
  Node { alloc = inc_alloc; reset = inc_reset ; step = inc_step }
type ('a) _use =
  { mutable i_70 : 'a }

let use  = 
  let Node { alloc = i_70_alloc; step = i_70_step ; reset = i_70_reset } = inc 
   in let use_alloc _ =
        ();{ i_70 = i_70_alloc () (* discrete *)  } in
  let use_reset self  =
    (i_70_reset self.i_70 :unit) in 
  let use_step self ((x_53:int): int) =
    ((let (y_54:int) = i_70_step self.i_70 x_53 in
      let (w_55:int) = (+) y_54  1 in
      w_55):int) in
  Node { alloc = use_alloc; reset = use_reset ; step = use_step }
type _chain = unit

let chain  = 
   let chain_alloc _ = () in
  let chain_reset self  =
    ((()):unit) in 
  let chain_step self ((x_56:int): int) =
    ((let (a_57:int) = (+) x_56  1 in
      let (b_58:int) = ( * ) a_57  2 in
      b_58):int) in
  Node { alloc = chain_alloc; reset = chain_reset ; step = chain_step }
let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_60 : 'e ;
    mutable h_67 : 'd ;
    mutable i_65 : 'c ; mutable h_63 : 'b ; mutable result_62 : 'a }

let main (cstate_71:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_60 = false ;
      h_67 = 42. ;
      i_65 = (false:bool) ; h_63 = (42.:float) ; result_62 = (():unit) } in
  let main_step self ((time_59:float) , ()) =
    ((self.major_60 <- cstate_71.major ;
      (let (result_76:unit) =
           let h_66 = ref (infinity:float) in
           (if self.i_65 then self.h_63 <- (+.) time_59  0.) ;
           (let (z_64:bool) = (&&) self.major_60  ((>=) time_59  self.h_63) in
            self.h_63 <- (if z_64 then (+.) self.h_63  dt else self.h_63) ;
            h_66 := min !h_66  self.h_63 ;
            self.h_67 <- !h_66 ;
            self.i_65 <- false ;
            (let (trigger_61:zero) = z_64 in
             (begin match trigger_61 with
                    | true ->
                        let () = () in
                        let (n_69:float) = theta in
                        let (r_68:float) = n_69 in
                        let _ = print_float r_68 in
                        self.result_62 <- print_newline ()
                    | _ -> self.result_62 <- ()  end) ; self.result_62)) in
       cstate_71.horizon <- min cstate_71.horizon  self.h_67 ; result_76)):
    unit) in  let main_reset self  =
                (self.i_65 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
