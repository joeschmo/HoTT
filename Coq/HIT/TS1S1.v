Add LoadPath "..".
Require Import Homotopy ExtensionalityAxiom MiscEquivalences Torus Circle.

Implicit Arguments base [c].
Implicit Arguments loop [c].

Parameter torus : Torus.
Parameter circle : Circle.

Lemma S1_face :
  (prod_path (idpath base) loop) @ (prod_path loop (idpath base)) ==
  (prod_path loop (idpath base)) @ (prod_path (idpath (@base circle)) (@loop circle)).
Proof.
  eapply concat.
  apply compose_prod_path.
  hott_simpl.
  apply opposite.
  eapply concat.
  apply compose_prod_path.
  hott_simpl.
Defined.
  
Definition torus_to_circles : torus -> circle * circle :=
  nd_torus_rect torus (circle * circle) (base , base) 
                      (prod_path loop (idpath base)) 
                      (prod_path (idpath base) loop) 
                      S1_face.

Definition circles_fst_loop_loop :
  transport (P := fun x => circle_rect' circle torus tbase loop2 x == circle_rect' circle torus tbase loop2 x)
            loop (compute_base' circle torus tbase loop2 @ loop1 @ !compute_base' circle torus tbase loop2)
  == (compute_base' circle torus tbase loop2 @ loop1 @ !compute_base' circle torus tbase loop2).
Proof.
  hott_simpl.
  eapply concat.
  apply trans_paths.
  apply concat_moveright_onright.
  rewrite compute_loop'.
  hott_simpl.
  unwhisker.
  apply concat_moveleft_onright.
  rewrite opposite_opposite.
  rewrite concat_associativity.
  apply concat_moveright_onleft.
  rewrite opposite_opposite.
  apply opposite.
  apply face.
Defined.

Definition circles_fst_loop_fibration : fibration circle :=
  fun x => circle_rect' circle torus tbase loop2 x == circle_rect' circle torus tbase loop2 x.

Definition circles_fst_loop : forall (x : circle), 
  circle_rect' circle torus tbase loop2 x == circle_rect' circle torus tbase loop2 x :=
  circle_rect circle
              (fun x => circle_rect' circle torus tbase loop2 x == 
                        circle_rect' circle torus tbase loop2 x)
              (compute_base' circle torus tbase loop2  @ loop1 @ !compute_base' circle torus tbase loop2)
              circles_fst_loop_loop.

Definition circles_to_torus' : circle -> circle -> torus :=
  circle_rect' circle (circle -> torus)
               (circle_rect' circle torus
                             tbase
                             loop2)
               (funext_dep _ _ _ _ circles_fst_loop).

Definition circles_to_torus (cs : circle * circle) : torus :=
  match cs with
    (c1 , c2) => circles_to_torus' c1 c2
  end.

Definition torus_circles_torus (t : torus) :
  circles_to_torus (torus_to_circles t) == t :=
  torus_rect torus
             (fun t => circles_to_torus (torus_to_circles t) == t)
             (idpath _)
             (idpath _)
             (idpath _).