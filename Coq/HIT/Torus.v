Add LoadPath "..".
Require Import Homotopy.
Require Import ExtensionalityAxiom.
Require Import MiscEquivalences.

Structure Torus := {
  torus :> Type;
  tbase : torus;
  loop1 : tbase == tbase;
  loop2 : tbase == tbase;
  face : loop2 @ loop1 == loop1 @ loop2;
  nd_torus_rect :
    (forall (P : Type) (pt : P) (lp1 lp2 : pt == pt) (f : lp2 @ lp1 == lp1 @ lp2),
      torus -> P);
  nd_compute_tbase :
    (forall P pt lp1 lp2 f,
      nd_torus_rect P pt lp1 lp2 f tbase == pt);
  nd_compute_loop1 :
    (forall P pt lp1 lp2 f,
      map (nd_torus_rect P pt lp1 lp2 f) loop1 ==
      nd_compute_tbase P pt lp1 lp2 f @ lp1 @ !(nd_compute_tbase P pt lp1 lp2 f));
  nd_compute_loop2 :
    (forall P pt lp1 lp2 f,
      map (nd_torus_rect P pt lp1 lp2 f) loop2 ==
      nd_compute_tbase P pt lp1 lp2 f @ lp2 @ !(nd_compute_tbase P pt lp1 lp2 f));
  torus_rect :
    (forall (P : torus -> Type) (pt : P tbase) 
            (lp1 : transport loop1 pt == pt)
            (lp2 : transport loop2 pt == pt)
            (f : transport (P := (fun x => transport x pt == pt)) face
                           (happly_dep (transport_comp P loop1 loop2) _ @
                            (map (transport loop1) lp2) @
                            lp1)
                 ==
                 (happly_dep (transport_comp P loop2 loop1) _ @
                  (map (transport loop2) lp1) @
                  lp2)),
     forall x : torus, P x);
  compute_tbase :
    (forall (P : torus -> Type) (pt : P tbase) 
            (lp1 : transport loop1 pt == pt)
            (lp2 : transport loop2 pt == pt)
            (f : transport (P := (fun x => transport x pt == pt)) face
                           (happly_dep (transport_comp P loop1 loop2) _ @
                            (map (transport loop1) lp2) @
                            lp1)
                 ==
                 (happly_dep (transport_comp P loop2 loop1) _ @
                  (map (transport loop2) lp1) @
                  lp2)),
     torus_rect P pt lp1 lp2 f tbase == pt);
  compute_loop1 :
    (forall P pt lp1 lp2 f,
      map_dep (torus_rect P pt lp1 lp2 f) loop1
      == map (transport loop1) (compute_tbase P pt lp1 lp2 f) @ lp1 @ !compute_tbase P pt lp1 lp2 f);
  compute_loop2 :
    (forall P pt lp1 lp2 f,
      map_dep (torus_rect P pt lp1 lp2 f) loop2
      == map (transport loop2) (compute_tbase P pt lp1 lp2 f) @ lp2 @ !compute_tbase P pt lp1 lp2 f)
}.

Implicit Arguments tbase [t].
Implicit Arguments loop1 [t].
Implicit Arguments loop2 [t].
Implicit Arguments face [t].

(*
Section Non_dependent.

  Variable torus : Torus.

  Definition torus_rect' :
    forall (B : Type) (pt : B) (lp1 lp2 : pt == pt) (f : lp2 @ lp1 == lp1 @ lp2), torus -> B.
  Proof.
    intros B pt' lp1' lp2' f'.
    apply torus_rect with (P := fun x => B) (pt := pt') (lp1 := trans_trivial loop1 pt') 
                          (lp2 := trans_trivial loop2 pt').
*)