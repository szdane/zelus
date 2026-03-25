(* The Zelus compiler, version 2.2-dev
  (2026-03-25-6:0) *)
open Ztypes
type ('a) _exec =
  { mutable m_32 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ m_32 = ((42 , 42):int * int) } in
  let exec_reset self  =
    (self.m_32 <- (4 , 2):unit) in 
  let exec_step self () =
    ((let ((next_33:int) , (next_34:int)) = self.m_32 in
      let (((y_30:int) , (z_31:int)): (int  * int)) = (next_33 , next_34) in
      self.m_32 <- ((( * ) ((+) z_31  1)  ((+) z_31  1)) , ((+) z_31  1)) ;
      y_30):int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
let dt = 0.1

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_36 : 'f ;
    mutable h_43 : 'e ;
    mutable i_41 : 'd ;
    mutable h_39 : 'c ; mutable result_38 : 'b ; mutable m_47 : 'a }

let main (cstate_50:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_36 = false ;
      h_43 = 42. ;
      i_41 = (false:bool) ;
      h_39 = (42.:float) ;
      result_38 = (():unit) ; m_47 = ((42 , 42):int * int) } in
  let main_step self ((time_35:float) , ()) =
    ((self.major_36 <- cstate_50.major ;
      (let (result_55:unit) =
           let h_42 = ref (infinity:float) in
           (if self.i_41 then self.h_39 <- (+.) time_35  0.) ;
           (let (z_40:bool) = (&&) self.major_36  ((>=) time_35  self.h_39) in
            self.h_39 <- (if z_40 then (+.) self.h_39  dt else self.h_39) ;
            h_42 := min !h_42  self.h_39 ;
            self.h_43 <- !h_42 ;
            self.i_41 <- false ;
            (let (trigger_37:zero) = z_40 in
             (begin match trigger_37 with
                    | true ->
                        let () = () in
                        let ((next_48:int) , (next_49:int)) = self.m_47 in
                        let (((y_45:int) , (z_46:int)): (int  * int)) =
                            (next_48 , next_49) in
                        self.m_47 <- ((( * ) ((+) z_46  1)  ((+) z_46  1)) ,
                                      ((+) z_46  1)) ;
                        (let (x_44:int) = y_45 in
                         let _ = print_int x_44 in
                         self.result_38 <- print_newline ())
                    | _ -> self.result_38 <- ()  end) ; self.result_38)) in
       cstate_50.horizon <- min cstate_50.horizon  self.h_43 ; result_55)):
    unit) in 
  let main_reset self  =
    ((self.i_41 <- true ; self.m_47 <- (4 , 2)):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
