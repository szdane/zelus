(* The Zelus compiler, version 2.2-dev
  (2025-10-31-20:23) *)
open Ztypes
let foo = (+) 2  1

let var = foo

let b = true

let foo2 = true

let dt = (+.) 0.1  0.3

let ite = if (>) foo  0 then ( * ) (-1)  foo else foo

type _test = unit

let test  = 
   let test_alloc _ = () in
  let test_reset self  =
    ((()):unit) in  let test_step self () =
                      ((+) 2  1:int) in
  Node { alloc = test_alloc; reset = test_reset ; step = test_step }
let f = 0

type _exec1 = unit

let exec1  = 
   let exec1_alloc _ = () in
  let exec1_reset self  =
    ((()):unit) in 
  let exec1_step self () =
    ((let ((n_38:int): int) = 5 in
      let ((e_37:int): int) = 5 in
      let (((x_39:int) , (y_40:int) , (z_41:int)): (int  * int  * int)) =
          (4 , 5 , 6) in
      e_37):int) in
  Node { alloc = exec1_alloc; reset = exec1_reset ; step = exec1_step }
type _exec = unit

let exec  = 
   let exec_alloc _ = () in
  let exec_reset self  =
    ((()):unit) in 
  let exec_step self () =
    ((let ((e_42:int): int) = 5 in
      7.):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_44 : 'e ;
    mutable h_51 : 'd ;
    mutable i_49 : 'c ; mutable h_47 : 'b ; mutable result_46 : 'a }

let main (cstate_54:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_44 = false ;
      h_51 = 42. ;
      i_49 = (false:bool) ; h_47 = (42.:float) ; result_46 = (():unit) } in
  let main_step self ((time_43:float) , ()) =
    ((self.major_44 <- cstate_54.major ;
      (let (result_59:unit) =
           let h_50 = ref (infinity:float) in
           (if self.i_49 then self.h_47 <- (+.) time_43  0.) ;
           (let (z_48:bool) = (&&) self.major_44  ((>=) time_43  self.h_47) in
            self.h_47 <- (if z_48 then (+.) self.h_47  dt else self.h_47) ;
            h_50 := min !h_50  self.h_47 ;
            self.h_51 <- !h_50 ;
            self.i_49 <- false ;
            (let (trigger_45:zero) = z_48 in
             (begin match trigger_45 with
                    | true ->
                        let () = () in
                        let ((e_53:int): int) = 5 in
                        let (x_52:float) = 7. in
                        let _ = print_float x_52 in
                        self.result_46 <- print_newline ()
                    | _ -> self.result_46 <- ()  end) ; self.result_46)) in
       cstate_54.horizon <- min cstate_54.horizon  self.h_51 ; result_59)):
    unit) in  let main_reset self  =
                (self.i_49 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
