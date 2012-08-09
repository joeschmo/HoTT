Add LoadPath "..".
Require Import Setoid.
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
(*  
  apply opposite.
  eapply concat.
  apply compose_prod_path.
  hott_simpl. *)
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

Definition circles_to_torus : (circle * circle) -> torus :=
  uncurry circles_to_torus'.

Definition torus_rect'
  (P : torus -> Type) (x : torus)
    (pt : P tbase)
    (lp1 : transport loop1 pt == pt)
           (lp2 : transport loop2 pt == pt)
           (f : transport (P := (fun x => transport x pt == pt)) face
                          (happly_dep (transport_comp P loop1 loop2) _ @
                           (map (transport loop1) lp2) @
                           lp1)
                ==
                (happly_dep (transport_comp P loop2 loop1) _ @
                 (map (transport loop2) lp1) @
                 lp2)) : P x :=
  torus_rect torus P pt lp1 lp2 f x.

Definition t_to_c_compute_tbase : torus_to_circles tbase == (base, base) :=
  nd_compute_tbase torus (circle * circle) (base, base) _ _ _.

Definition c_to_c_compute_base :
  circle_rect' circle (circle -> torus) (circle_rect' circle torus tbase loop2) 
               (funext_dep circle (fun _ : circle => torus)
                 (circle_rect' circle torus tbase loop2)
                 (circle_rect' circle torus tbase loop2) circles_fst_loop)
               base base
  == circle_rect' circle torus tbase loop2 base :=
  happly (compute_base' circle (circle -> torus) (circle_rect' circle torus tbase loop2) _) base.

Definition c_to_t_compute_bases :
  circle_rect' circle torus tbase loop2 base == tbase :=
  compute_base' circle torus tbase loop2.

Definition idpth : circles_to_torus (torus_to_circles tbase) == tbase :=
  map circles_to_torus t_to_c_compute_tbase @ c_to_c_compute_base @ c_to_t_compute_bases.

Definition q' : 
  (fun x : circle => circles_to_torus' x (snd (torus_to_circles tbase))) ==
  (fun x : circle => circles_to_torus' x base) :=
  map (fun y => (fun x : circle => circles_to_torus' x y)) (map (fun xy => snd xy) t_to_c_compute_tbase).

Definition idpth_to_idpath :
    !compute_base' circle torus tbase loop2 @
    !happly
        (compute_base' circle (circle -> torus)
          (circle_rect' circle torus tbase loop2)
          (funext_dep circle (fun _ : circle => torus)
            (circle_rect' circle torus tbase loop2)
            (circle_rect' circle torus tbase loop2) circles_fst_loop)) base @
    !happly q' (fst (base, base)) @
    !map
        (fun x : circle =>
          circle_rect' circle (circle -> torus)
            (circle_rect' circle torus tbase loop2)
            (funext_dep circle (fun _ : circle => torus)
              (circle_rect' circle torus tbase loop2)
              (circle_rect' circle torus tbase loop2) circles_fst_loop)
            x (snd (torus_to_circles tbase)))
        (nd_fst_path
          (nd_compute_tbase torus (circle * circle)
            (base, base) (prod_path loop (idpath base))
            (prod_path (idpath base) loop) S1_face)) @
    idpth ==
    idpath tbase.
Proof.
  unfold idpth.  
  unfold t_to_c_compute_tbase.
  unfold c_to_c_compute_base.
  unfold c_to_t_compute_bases.
  unfold circles_to_torus.
  unfold uncurry.
  unfold circles_to_torus'.
  simpl.
  associate_right.
  
Defined.

Lemma torus_circles_torus :
  forall (t : torus), circles_to_torus (torus_to_circles t) == t.
Proof.
  intros t.
  set (P := fun t => circles_to_torus (torus_to_circles t) == t).
  
  assert (trans_loop1 : transport (P := P)
                                  loop1 idpth == idpth).
    eapply concat.  
    apply trans_paths with (f := fun t => circles_to_torus (torus_to_circles t)) (g := fun t => t).
    hott_simpl.  
    rewrite concat_associativity.
    apply concat_moveright_onleft.
    hott_simpl.
    apply opposite.
    rewrite map_comp.
    unfold torus_to_circles.
    rewrite nd_compute_loop1.
    unfold circles_to_torus.
    unfold circles_to_torus'.

    rewrite map_uncurry.
    rewrite map2_maps_1.
    rewrite nd_snd_path_dist.
    rewrite nd_snd_path_dist.
    rewrite concat_map.
    rewrite concat_map.
    rewrite snd_prod_path.
    rewrite idpath_map.
    rewrite nd_snd_path_opp.
    hott_simpl.
(*
    rewrite nd_fst_path_dist.
    rewrite nd_fst_path_dist.
    rewrite concat_map.
    rewrite concat_map.
    rewrite fst_prod_path.
    apply concat_moveright_onright.
    rewrite nd_fst_path_opp.
    rewrite opposite_map.
  *)    
    fold torus_to_circles.
    fold circles_to_torus'.
    apply concat_moveright_onleft.
    rewrite concat_associativity.
    apply concat_moveright_onleft.
    apply concat_moveright_onright.

    rewrite map_cong with (q := q').
    apply concat_moveright_onright.
    apply concat_moveright_onleft.
    rewrite map_app.
    unfold circles_to_torus'.
    rewrite compute_loop'.
    rewrite happly_concat.
    rewrite happly_concat.
    rewrite happly_funext_dep_compute.
    apply concat_moveright_onright.
    apply concat_moveright_onleft.
    unfold circles_fst_loop.
    rewrite compute_base.
    fold circles_fst_loop.
    apply concat_moveright_onright.
    apply concat_moveright_onleft.

    apply opposite.
    admit.

    
  assert (trans_loop2 : transport (P := P)
                                  loop2 idpth == idpth).
    eapply concat.
    apply trans_paths with (f := fun t => circles_to_torus (torus_to_circles t)) (g := fun t => t).
    hott_simpl.
    rewrite concat_associativity.
    apply concat_moveright_onright.
    apply opposite.
    hott_simpl.
    apply opposite.
    rewrite map_comp.
    unfold torus_to_circles.
    rewrite nd_compute_loop2.
    unfold circles_to_torus.
    unfold circles_to_torus'.
    rewrite map_uncurry.
    rewrite map2_maps_1.
    rewrite nd_fst_path_dist.
    rewrite nd_fst_path_dist.
    rewrite concat_map.
    rewrite concat_map.
    rewrite fst_prod_path.
    rewrite idpath_map.
    rewrite nd_fst_path_opp.
    hott_simpl.
    rewrite nd_snd_path_dist.
    rewrite nd_snd_path_dist.
    rewrite concat_map.
    rewrite concat_map.
    hott_simpl.
    rewrite snd_prod_path.
    rewrite nd_snd_path_opp.
    rewrite opposite_map.
    rewrite opposite_opposite.
    
    fold torus_to_circles.
    fold circles_to_torus'.

    admit.
  apply torus_rect with (P := P)
                        (pt := idpth) (lp1 := trans_loop1) (lp2 := trans_loop2).
  