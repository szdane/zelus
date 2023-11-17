(* The Zelus compiler, version 2.2-dev
  (2023-10-14-18:6) *)
open Ztypes
let vfi = 0.8

let dt = 0.1

let b = 0.136

let xl = 5.

type _max = unit

let max  = 
   let max_alloc _ = () in
  let max_reset self  =
    ((()):unit) in 
  let max_step self ((x_59:float): float) =
    (((if (<) x_59  0. then 0. else x_59)):float) in
  Node { alloc = max_alloc; reset = max_reset ; step = max_step }
type _control = unit

let control  = 
   let control_alloc _ = () in
  let control_reset self  =
    ((()):unit) in 
  let control_step self (((d_60:float) , (vcontrol_61:float)): (float  *
                                                                float)) =
    (((if (<=) ((-.) ((-.) ((-.) d_60 
                                 ((/.) (( *. ) vcontrol_61  vcontrol_61) 
                                       (( *. ) 2.  b))) 
                           (( *. ) vcontrol_61  dt)) 
                     ((/.) (( *. ) vcontrol_61  dt)  2.))  0.5
       then (~-.) b
       else 0.)):float) in
  Node { alloc = control_alloc; reset = control_reset ; step = control_step }
type ('d , 'c , 'b , 'a) _exec =
  { mutable i_95 : 'd ;
    mutable i_94 : 'c ; mutable i_71 : 'b ; mutable m_67 : 'a }

let exec  = 
  let Node { alloc = i_95_alloc; step = i_95_step ; reset = i_95_reset } = max 
   in 
  let Node { alloc = i_94_alloc; step = i_94_step ; reset = i_94_reset } = control 
   in
  let exec_alloc _ =
    ();
    { i_71 = (false:bool) ; m_67 = ((42. , 42. , 42.):float * float * float);
      i_95 = i_95_alloc () (* discrete *)  ;
      i_94 = i_94_alloc () (* discrete *)  } in
  let exec_reset self  =
    ((self.i_71 <- true ; i_95_reset self.i_95  ; i_94_reset self.i_94 ):
    unit) in 
  let exec_step self () =
    (((if self.i_71 then self.m_67 <- (xl , vfi , 0.)) ;
      self.i_71 <- false ;
      (let ((x_68:float) , (x_69:float) , (x_70:float)) = self.m_67 in
       let (((df_63:float) , (vf_64:float) , (af_62:float)): (float  *
                                                              float  * float)) =
           (x_68 , x_69 , x_70) in
       let (v_next_65:float) =
           i_95_step self.i_95 ((+.) vf_64  (( *. ) af_62  dt)) in
       let (d_next_66:float) = (-.) df_63  (( *. ) v_next_65  dt) in
       self.m_67 <- (d_next_66 ,
                     v_next_65 ,
                     (i_94_step self.i_94 (d_next_66 , v_next_65))) ;
       (df_63 , vf_64 , af_62))):float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_97 : 'i ;
    mutable i_96 : 'h ;
    mutable major_73 : 'g ;
    mutable h_80 : 'f ;
    mutable i_78 : 'e ;
    mutable h_76 : 'd ;
    mutable result_75 : 'c ; mutable i_93 : 'b ; mutable m_89 : 'a }

let main (cstate_98:Ztypes.cstate) = 
  let Node { alloc = i_97_alloc; step = i_97_step ; reset = i_97_reset } = max 
   in 
  let Node { alloc = i_96_alloc; step = i_96_step ; reset = i_96_reset } = control 
   in
  let main_alloc _ =
    ();
    { major_73 = false ;
      h_80 = 42. ;
      i_78 = (false:bool) ;
      h_76 = (42.:float) ;
      result_75 = (():unit) ;
      i_93 = (false:bool) ; m_89 = ((42. , 42. , 42.):float * float * float);
      i_97 = i_97_alloc () (* discrete *)  ;
      i_96 = i_96_alloc () (* discrete *)  } in
  let main_step self ((time_72:float) , ()) =
    ((self.major_73 <- cstate_98.major ;
      (let (result_103:unit) =
           let h_79 = ref (infinity:float) in
           (if self.i_78 then self.h_76 <- (+.) time_72  0.) ;
           (let (z_77:bool) = (&&) self.major_73  ((>=) time_72  self.h_76) in
            self.h_76 <- (if z_77 then (+.) self.h_76  dt else self.h_76) ;
            h_79 := min !h_79  self.h_76 ;
            self.h_80 <- !h_79 ;
            self.i_78 <- false ;
            (begin match z_77 with
                   | true ->
                       (if self.i_93 then self.m_89 <- (xl , vfi , 0.)) ;
                       self.i_93 <- false ;
                       (let ((x_90:float) , (x_91:float) , (x_92:float)) =
                            self.m_89 in
                        let (((df_85:float) , (vf_86:float) , (af_84:float)): 
                            (float  * float  * float)) = (x_90 , x_91 , x_92) in
                        let (v_next_87:float) =
                            i_97_step self.i_97
                              ((+.) vf_86  (( *. ) af_84  dt)) in
                        let (d_next_88:float) =
                            (-.) df_85  (( *. ) v_next_87  dt) in
                        self.m_89 <- (d_next_88 ,
                                      v_next_87 ,
                                      (i_96_step self.i_96
                                         (d_next_88 , v_next_87))) ;
                        (let _ = print_float df_85 in
                         let _ = print_string "," in
                         let _ = print_float vf_86 in
                         let _ = print_string "," in
                         let _ = print_float af_84 in
                         self.result_75 <- print_newline ()))
                   | _ -> self.result_75 <- ()  end) ; self.result_75) in
       cstate_98.horizon <- min cstate_98.horizon  self.h_80 ; result_103)):
    unit) in 
  let main_reset self  =
    ((self.i_78 <- true ;
      self.i_93 <- true ; i_97_reset self.i_97  ; i_96_reset self.i_96 ):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
