Require Import Paths Fibrations Equivalences 
               Funext Univalence ExtensionalityAxiom 
               UnivalenceImpliesFunext.

(*
NOTES TO SELF:
@ has the reverse argument order of path composition in agda
*)

Definition concat_opposite A (x y z : A) (p : x == y) (q : y == z) : !q @ !p == !(p @ q).
Proof.
  path_induction.
Defined.

Definition nd_fst_path {A B} {p q : A * B} : (p == q) -> (fst p) == (fst q).
Proof.
  intros.
  path_induction.
Defined.

Definition nd_snd_path {A B} {p q : A * B} : (p == q) -> (snd p) == (snd q).
Proof.
  intros.
  path_induction.
Defined.

(* Distributive property of nd_fst_path and nd_snd_path *)

Definition nd_fst_path_dist A B {m n r : A * B} (p : m == n) (q : n == r) :
  nd_fst_path (p @ q) == nd_fst_path p @ nd_fst_path q.
Proof.
  path_induction.
Defined.

Hint Rewrite nd_fst_path_dist : paths.

Definition nd_snd_path_dist A B {m n r : A * B} (p : m == n) (q : n == r) :
  nd_snd_path (p @ q) == nd_snd_path p @ nd_snd_path q.
Proof.
  path_induction.
Defined.

Hint Rewrite nd_snd_path_dist : paths.

(* Computation rule for nd_fst_path and nd_snd_path *)

Definition fst_prod_path A B {m m' : A} {n n' : B} (p : m == m') (q : n == n') :
  nd_fst_path (prod_path p q) == p.
Proof.
  path_induction.
Defined.

Hint Rewrite fst_prod_path : paths.

Definition snd_prod_path A B {m m' : A} {n n' : B} (p : m == m') (q : n == n') :
  nd_snd_path (prod_path p q) == q.
Proof.
  path_induction.
Defined.

Hint Rewrite snd_prod_path : paths.

(* Extracting opposite from within a fst_path or snd_path *)

Definition nd_fst_path_opp A B {m m' : A * B} (p : m == m') :
  nd_fst_path (! p) == !nd_fst_path p.
Proof.
  path_induction.
Defined.

Hint Rewrite nd_fst_path_opp : paths.

Definition nd_snd_path_opp A B {m m' : A * B} (p : m == m') :
  nd_snd_path (! p) == !nd_snd_path p.
Proof.
  path_induction.
Defined.

Hint Rewrite nd_snd_path_opp : paths.

Lemma compose_prod_path A {m n p q r s : A} (a : n == p) (b : r == s) (c : m == n) (d : q == r):
  (prod_path c d) @ (prod_path a b) == (prod_path (c @ a) (d @ b)).
Proof.
  path_induction.
Defined.

Hint Rewrite compose_prod_path : paths.

Lemma map_compose_fst A B {m n : A} (f : A -> B) (y : B) (p : m == n) :
  map (fun x => (f(x) , y)) p == prod_path (map (fun x => f x) p) (map (fun _ => y) p).
Proof.
  path_induction.
Defined.

Hint Rewrite map_compose_fst : paths.

Lemma map_compose_snd A B {m n : A} (f : A -> B) (y : B) (p : m == n) :
  map (fun x => (y , f(x))) p == prod_path (map (fun _ => y) p) (map (fun x => f x) p).
Proof.
  path_induction.
Defined.

Hint Rewrite map_compose_snd : paths.

Lemma transport_prod G {t1 t2 : G} (d : t1 == t2) (a : G -> Type) (b : G -> Type) :
  transport (P := fun z => prod (a z) (b z)) d == 
  (fun p => (transport (P := a) d (fst p) , transport (P := b) d (snd p))).
Proof.
  path_induction.
  by_extensionality.
Defined.

Hint Rewrite transport_prod : paths.

Definition double_map {A B C} {m n : A} {m' n' : B} (f : A -> B -> C) : 
  (m == n) -> (m' == n') -> (f m m') == (f n n').
Proof.
  intros.
  path_induction.
Defined.

Lemma map2_maps_1 A B C {m n : A} {m' n' : B} (f : A -> B -> C) (p : m == n) (q : m' == n') :
  double_map f p q == map (fun y => f m y) q @ map (fun x => f x n') p.
Proof.
  path_induction.
Defined.

Hint Rewrite map2_maps_1 : paths.

Lemma map2_maps_2 A B C {m n : A} {m' n' : B} (f : A -> B -> C) (p : m == n) (q : m' == n') :
  double_map f p q == map (fun x => f x m') p @ map (fun y => f n y) q.
Proof.
  path_induction.
Defined.

Hint Rewrite map2_maps_2 : paths.

Definition uncurry {A B C : Type} (f : A -> B -> C) : (A * B) -> C :=
  fun xy => f (fst xy) (snd xy).

Lemma map_uncurry A B C (f : A -> B -> C) {p q : A * B} (x : p == q) :
  map (uncurry f) x == double_map f (nd_fst_path x) (nd_snd_path x).
Proof.
  induction x.
  path_induction.
Defined.

Hint Rewrite map_uncurry : paths.

(*
A more comprehensive version of the above proof, i.e. without the use of the nuclear-grade 
tactic 'by_extensionality'. Presented here to help better understand how to use the 
function extensionality axiom and lemmas.
 
Proof.
  induction d.
  apply funext_dep.
  unfold ext_dep_eq.
  intros.
  simpl.
  induction x.
  simpl.
  apply idpath.
Defined.
*)


Lemma map_comp {A B C : Type} (g : B -> C) (f : A -> B) {m n : A} (p : m == n) :
  map (fun x => g (f x)) p == map g (map f p).
Proof.
  path_induction.
Defined.

Lemma transport_comp {A : Type} (C : A -> Type) {m n p : A} (b : n == p) (a : m == n) :
  transport (P := C) (a @ b) == (fun x => transport (P := C) b (transport (P := C) a x)).
Proof.
  by_extensionality.
  hott_simpl.
Defined.

Lemma map_cong {A B : Type} (f g : A -> B) {m n : A} (q : g == f) (p : m == n) :
  map g p == happly q m @ map f p @ ! happly q n.
Proof.
  path_induction.
Defined.

Lemma map_app {G A B : Type} {t1 t2 : G} {d : t1 == t2} {f : G -> A -> B} {m : A} :
  map (fun x => (f x) m) d == happly (map f d) m.
Proof.
  path_induction.
Defined.

Lemma happly_funext_dep_compute
  (X Y : Type) (f g : X -> Y) (p : f === g) (x : X) :
  happly (funext_dep X _ f g p) x == p x.
Proof.
  admit.
Defined.
  

Hint Resolve
  map_uncurry
  map2_maps_1 map2_maps_2
  nd_fst_path_dist nd_snd_path_dist
  fst_prod_path snd_prod_path
  nd_fst_path_opp nd_snd_path_opp
  compose_prod_path
  map_compose_fst map_compose_snd
  transport_prod
 : path_hints_misc.

Ltac hott_simpl_misc :=
  autorewrite with paths in * |- * ; auto with path_hints_misc.