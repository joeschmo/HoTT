Require Import Paths Fibrations Equivalences 
               Funext Univalence ExtensionalityAxiom 
               UnivalenceImpliesFunext.

(*
NOTES TO SELF:
@ has the reverse argument order of path composition in agda
*)

Lemma compose_prod_path {A} {m n p q r s : A} (a : n == p) (b : r == s) (c : m == n) (d : q == r):
  (prod_path c d) @ (prod_path a b) == (prod_path (c @ a) (d @ b)).
Proof.
  path_induction.
Defined.

Lemma map_compose_fst {A B} {m n : A} (f : A -> B) (y : B) (p : m == n) :
  map (fun x => (f(x) , y)) p == prod_path (map (fun x => f x) p) (map (fun _ => y) p).
Proof.
  path_induction.
Defined.

Lemma map_compose_snd {A B} {m n : A} (f : A -> B) (y : B) (p : m == n) :
  map (fun x => (y , f(x))) p == prod_path (map (fun _ => y) p) (map (fun x => f x) p).
Proof.
  path_induction.
Defined.

Lemma transport_prod {G} {t1 t2 : G} (d : t1 == t2) (a : G -> Type) (b : G -> Type) :
  transport (P := fun z => prod (a z) (b z)) d == 
  (fun p => (transport (P := a) d (fst p) , transport (P := b) d (snd p))).
Proof.
  induction d.
  by_extensionality.
Defined.

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

Lemma transport_comp {A : Type} (C : A -> Type) {m n p : A} (b : n == p) (a : m == n) :
  transport (P := C) (a @ b) == (fun x => transport (P := C) b (transport (P := C) a x)).
Proof.
  by_extensionality.
  hott_simpl.
Defined.

