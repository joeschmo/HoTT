Add LoadPath "..".
Require Import Homotopy.
Require Import ExtensionalityAxiom.
Require Import MiscEquivalences.

Structure Torus := {
  torus :> Type;
  base : torus;
  loop1 : base == base;
  loop2 : base == base;
  face : loop2 @ loop1 == loop1 @ loop2;
  torus_rect :
    (forall (P : torus -> Type) (pt : P base) 
            (lp1 : transport loop1 pt == pt)
            (lp2 : transport loop2 pt == pt)
            (f : transport (P := (fun x => transport x pt == pt)) face
                           (happly_dep (transport_trans P loop1 loop2) @
                            (map (transport loop1) lp2) @
                            lp1)
                 ==
                 (happly_dep (transport_trans P loop2 loop1) @
                  (map (transport loop2) lp1) @
                  lp2)),
     forall x : torus, P x)
}.