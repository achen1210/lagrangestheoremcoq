(** * Andrew Chen
3/13/22 *)

From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Coq.Program.Program.
Require Import Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Sets.Ensembles.
Require Import Coq.ZArith.Int. (*would like to use integers, but did not
                                 realize it was necessary until it was too late *)

(*Basic group definitions and properties, showing group axioms from left axioms.*)

Class Group (G : Type) : Type := 
{
  op : G -> G -> G;
  inv : G -> G;
  e : G;

  associativity : forall a b c, op a (op b c) = op (op a b) c;
  leftidentity : forall a, op e a = a;
  leftinverse : forall a, op (inv a) a = e;
}.

Class Finite (G : Type) : Type :=
{
  elements : list G;
}.

Class FiniteGroup (G : Type) {g : Group G} {f : Finite G} : Type := { }.

(*Class FiniteGroup (G : Type) {g : Group G}: Type :=
{
  elements : list G;
  (*
  (*cardinality := length(elements);*)
  memberfinitegroup (m : G) : Prop := In m elements <-> member m*)
}. *)

Definition finiteorder {G : Type}{g : Group G}{f : Finite G}{f : FiniteGroup G} : nat :=
  length(elements).

(*Definition isfinitegroup (G : Type){g : Group G}{f : Finite G}{f : FiniteGroup G} : Prop :=
  forall (g : G), In g elements. *)

Notation "x '**' y" := (op x y) (at level 50, left associativity).

Definition idempotent {G : Type} {g : Group G} (a : G) : Prop := 
  op a a = a.

Definition identity {G : Type} {g : Group G} (a : G) : Prop :=
  a = e.

Lemma leftapplication {G : Type} {g : Group G} : forall (a b c: G),
  a = b -> c ** a = c ** b.
Proof.
  intros. rewrite H. reflexivity.
Qed.

Lemma rightapplication {G : Type} {g : Group G} : forall (a b c : G), 
  a = b -> a ** c = b ** c.  
Proof.
  intros. rewrite H. reflexivity. 
Qed.

Theorem rightinverse {G : Type} {g : Group G} : forall (a : G),
  op a (inv a) = e. (*hard*)
Proof.
  intros. rewrite <- leftidentity with (a ** inv a). 
  rewrite <- leftinverse with (a ** inv a).
  rewrite <- associativity.
  assert (A: a ** inv a ** (a ** inv a) = a ** (inv a ** a) ** inv a).
  { rewrite associativity. rewrite associativity. reflexivity. }
   rewrite A. rewrite leftinverse with a. rewrite <- associativity. 
   rewrite leftidentity. reflexivity.
Qed.

Theorem rightidentity {G : Type} {g : Group G} : forall (a : G),
  a ** e = a.
Proof.
  intros. rewrite <- leftinverse with a.
  rewrite associativity. rewrite rightinverse with a.
  rewrite leftidentity. reflexivity. 
Qed.

Lemma leftcancellation {G : Type} {g : Group G} : forall (a b c : G), 
  c ** a = c ** b -> a = b.  
Proof.
  intros. rewrite <- leftidentity. rewrite <- leftinverse with c.
  rewrite <- associativity. rewrite <- H. rewrite associativity.
  rewrite leftinverse. rewrite leftidentity. reflexivity. 
Qed.

Lemma rightcancellation {G : Type} {g : Group G} : forall (a b c : G), 
  a ** c = b ** c -> a = b.  
Proof.
  intros. rewrite <- rightidentity. rewrite <- rightinverse with c.
  rewrite associativity. rewrite <- H. rewrite <- associativity.
  rewrite rightinverse. rewrite rightidentity. reflexivity. 
Qed.

Theorem inverse_unique {G : Type} {g : Group G}: forall (a b: G),
  a ** b = e -> a = inv b /\  b = inv a.
Proof.
  intros. split.
  * rewrite <- leftidentity. rewrite <- H.
    rewrite <- associativity.
    rewrite rightinverse with b. rewrite rightidentity. reflexivity.
  * rewrite <- rightidentity. rewrite <- H.
    rewrite associativity.
    rewrite leftinverse with a. rewrite leftidentity. reflexivity.
Qed.

Lemma inverseinverse {G : Type} {g : Group G} : forall (a : G), 
  inv (inv a) = a.
Proof. 
  intros. 
  remember (leftinverse a) as H.
  destruct HeqH. apply inverse_unique in H. destruct H.
  symmetry. assumption.
Qed. 

Lemma inversefunction {G : Type} {g : Group G} : forall (a b : G), 
  a = b -> inv a = inv b. 
Proof.
  intros. rewrite H; reflexivity.
Qed.

Lemma inverseinjective {G : Type} {g : Group G} : forall (a b : G), 
  inv a = inv b -> a = b. 
Proof.
  intros. apply inversefunction in H. repeat rewrite inverseinverse in H. assumption.
Qed. 

Theorem inversedistribution {G : Type} {g : Group G} : forall (a b : G), 
 inv (a ** b) = inv b ** inv a.
Proof.
  intros. rewrite <- rightcancellation with (inv (a ** b)) (inv b ** inv a) a. reflexivity.
  rewrite <- associativity. rewrite leftinverse with a. rewrite rightidentity.
  rewrite <- rightcancellation with (inv (a ** b) ** a) (inv b) b. reflexivity.
  rewrite leftinverse with b. rewrite <- associativity. rewrite leftinverse with (a ** b).
  reflexivity.
Qed.

Lemma einverse_ise {G : Type} {g : Group G} : forall (a : G), 
  inv e = e.
Proof. 
  intros. rewrite <- leftidentity with (inv e). rewrite rightinverse with e. reflexivity.
Qed. 

Theorem leftinverseisrightinverse {G : Type} {g : Group G}: forall (a b c: G),
  a ** b = e /\ c ** a = e -> b = c.
Proof.
  intros. destruct H. apply leftapplication with (c ** a) e (inv c) in H0. 
  rewrite associativity in H0. rewrite leftinverse in H0. rewrite leftidentity in H0.
  rewrite rightidentity in H0. rewrite H0 in H. apply inverse_unique in H. destruct H.
  apply inverseinjective in H. symmetry; assumption.
Qed.

Theorem inversecommutes {G : Type} {g : Group G}: forall (a b: G),
  a ** b = e <-> b ** a = e.
Proof.
  intros. split; intros.
  * rewrite <- rightinverse with b. rewrite <- leftapplication with a (inv b) b. reflexivity.
    rewrite <- leftinverse with b in H. apply rightcancellation in H. assumption.
  * rewrite <- rightinverse with a. rewrite <- leftapplication with b (inv a) a. reflexivity.
    rewrite <- leftinverse with a in H. apply rightcancellation in H. assumption.
Qed.
   
Lemma leftidentity_unique {G : Type}{g : Group G}: forall (a b : G), 
  a ** b = b -> a = e.
Proof.
  intros. rewrite <- leftidentity with b in H.
  rewrite associativity in H. rewrite rightidentity with a in H.
  rewrite rightcancellation with a e b. reflexivity. assumption. 
Qed.

Lemma rightidentity_unique {G : Type}{g : Group G}: forall (a b : G), 
  a ** b = a -> b = e.
Proof.
  intros. rewrite <- rightidentity with a in H.
  rewrite <- associativity in H. rewrite leftidentity with b in H.
  rewrite leftcancellation with b e a. reflexivity. assumption. 
Qed.

Theorem leftidentityisrightidentity {G : Type} {g : Group G}: forall (a b c: G),
  a ** b = a /\ c ** a = a -> b = c.
Proof.
  intros. destruct H. rewrite <- leftidentity in H0. apply rightcancellation in H0.
  rewrite <- rightidentity in H. apply leftcancellation in H. rewrite <- H in H0. symmetry.
  assumption.
Qed.

Theorem idempotent_is_identity {G : Type} {g : Group G} : forall (a : G), 
idempotent a <-> identity a.  
Proof.
  intros. split; intros.
  * inversion H. unfold identity. rewrite <- leftidentity in H0. apply rightcancellation in H0.
    rewrite H0. apply rightidentity.
  * inversion H. unfold idempotent. apply rightidentity.
Qed.

(*Cyclic and Abelian groups *)

Class AbelianGroup (G : Type) {g : Group G} : Type :=
{
  commutativity : forall a b, op a b = op b a
}. 

Definition iscommutative {G : Type} {g : Group G} (a b : G) : Prop := 
  a ** b = b ** a.

Definition isabelian (G : Type) {g : Group G} : Prop := 
  forall (a b: G), iscommutative a b. 

Fixpoint opexponent {G : Type} {g : Group G}(base : G)(n : nat): G :=
  match n with
  | O => e 
  | S n => base ** opexponent base n 
end.

Class CyclicGroup (G : Type) {g : Group G} : Type :=
{
  generator : exists a, forall b, exists (n : nat), opexponent a n = b
}. 

Definition iscyclic (G : Type) {g : Group G} : Prop :=
  exists (a : G), forall (b : G), exists (n : nat), opexponent a n = b.

Definition isgenerator {G : Type} {g : Group G} (gen : G) : Prop :=
  forall b, exists (n : nat), opexponent gen n = b.

Lemma opexponentaddition {G : Type}{g : Group G}: forall (a : G) (n1 n2 : nat),
  (opexponent a n1) ** (opexponent a n2) = (opexponent a (n1 + n2)) /\ 
  (opexponent a n2) ** (opexponent a n1) = (opexponent a (n1 + n2)).
Proof.
  intros. split.
  * induction n1. simpl. apply leftidentity.
    simpl. rewrite <- associativity. 
    rewrite leftapplication with (opexponent a n1 ** opexponent a n2) (opexponent a (n1 + n2)) a.
    reflexivity. assumption.
  * induction n2. simpl. rewrite leftidentity. rewrite plus_0_r. reflexivity.
    assert (A: n1 + S n2 = S n2 + n1).
    { lia. }
    rewrite A. simpl. rewrite <- associativity. 
    rewrite leftapplication with (opexponent a n2 ** opexponent a n1) (opexponent a (n2 + n1)) a.
    reflexivity.
    assert (B : n2 + n1 = n1 + n2).
    { lia. }
    rewrite B; assumption.
Qed.

Theorem cyclicisabelian (G : Type){g : Group G}{c : CyclicGroup G} : 
  isabelian G.
Proof.
  unfold isabelian. unfold iscommutative. intros. inversion c. destruct generator0.
  assert (A: exists n1, opexponent x n1 = a).
  { eapply H. }
  assert (B: exists n1, opexponent x n1 = b).
  { eapply H. }
  destruct A. destruct B.
  rewrite <- H0. rewrite <- H1.
  assert (X: opexponent x x0 ** opexponent x x1 = opexponent x (x0+x1)).
  {apply opexponentaddition. }
  assert (Y : opexponent x x1 ** opexponent x x0 = opexponent x (x0+x1)).
  {apply opexponentaddition. }
  rewrite X. rewrite Y. reflexivity.
Qed.

(*Defining Subgroups*)

Class Restrict (G : Type) : Type := 
{
  member : G -> Prop
}.

Class Subgroup (G : Type){g : Group G}{r : Restrict G} : Type :=
{
  closure : forall a b, member a -> member b -> member (op a b);
  inverse : forall a, member a -> member (inv a);
  identityinsubgroup : forall a, identity a -> member a
}.

Class FiniteSubgroup (G : Type){g : Group G}{r : Restrict G}{f : Finite G} : Type := {}.

Definition subgroupfiniteorder {G : Type}{g : Group G}{r : Restrict G}{f : Finite G}{fg : FiniteSubgroup G} : nat :=
  length(elements).

Definition issubgroup {G : Type}{g : Group G}(r : Restrict G) : Prop :=
  forall (a b : G), member a -> member b -> member e /\ member (a ** b) /\ member (inv a).

(*Informally, if G is a group and a is in G, then H = { a ^ n | n \in Z} is a subgroup of G
  containing a. This is the smallest subgroup containing a, as subgroups must be closed 
  under operation. *)
Theorem smallestsubgroupcontaininga {G : Type}{g : Group G}{r : Restrict G} : 
  forall (a : G), ((forall (n : nat), member (opexponent a n)) /\ 
                  (forall (b : G), member b -> (exists (n: nat), b = opexponent a n))) 
                  -> issubgroup r.
Proof.
  intros. unfold issubgroup. intros. split.
  * assert (B: member (opexponent a 0)).
    { intros. apply H. }
    simpl in B. assumption. 
  * split; destruct H.
    - apply H2 in H1. apply H2 in H0. destruct H1. destruct H0.
      rewrite H0. rewrite H1.
      assert(A : opexponent a x0 ** opexponent a x = opexponent a (x0 + x)).
      { apply opexponentaddition. }
      rewrite A. apply H.
    - apply H2 in H0. destruct H0. rewrite H0. 
      (*At the point the informal proof relies on the usage of Z,
        namely the existence of -x,
        but here I only have the naturals in the form of nat. *)
Admitted.

Class NormalSubgroup (G : Type){g : Group G}{r : Restrict G}{h : Subgroup G} : Type :=
{
  normal : forall (g n : G), member n -> member (g ** n ** (inv g))
}.

Lemma onenonmemberleadstononmember{G : Type}{g : Group G}{r : Restrict G}{h : Subgroup G} : forall (a b : G), 
 (~(member a) /\ member b ) \/ (member a /\ ~(member b)) -> ~(member (a ** b)).
 Proof.
  intros. remember closure as A. destruct H.
  * destruct H. unfold not. unfold not in H. intros. apply H.
    apply inverse in H0. apply A with (a ** b) (inv b) in H0.
    rewrite <- associativity in H0. rewrite rightinverse with b in H0. rewrite rightidentity in H0.
    assumption. assumption.
  * destruct H. unfold not. unfold not in H. intros. apply H0.
    apply inverse in H. apply A with (inv a) (a ** b) in H.
    rewrite associativity in H. rewrite leftinverse with a in H. rewrite leftidentity in H.
    assumption. assumption.
Qed.

Lemma subgroupinverse {G : Type}{g : Group G}{r : Restrict G}{h : Subgroup G} : forall (a : G),
  member(inv a) <-> member a. 
Proof.
  intros. split; intros.
  * apply inverse in H. rewrite inverseinverse with a in H. assumption.
  * apply inverse in H; assumption. 
Qed.

Lemma notsubgroupinverse {G : Type}{g : Group G}{r : Restrict G}{h : Subgroup G} : forall (a : G),
  ~member(inv a) <-> ~member a.
Proof.
  intros. split; intros.
  * unfold not. intros. unfold not in H. apply H. apply inverse in H0. assumption.
  * unfold not. unfold not in H. intros. apply H. rewrite subgroupinverse in H0. assumption.
Qed. 

Lemma subgroupleftmember {G : Type}{g : Group G}{r : Restrict G}{h : Subgroup G} : forall (a b : G),
  member a -> member b <-> member(a ** b).
Proof.
  intros; split; intros.
  * apply closure with a b in H. assumption. assumption.
  * apply inverse in H. apply closure with (inv a) (a ** b) in H. rewrite associativity in H.
    rewrite leftinverse in H. rewrite leftidentity in H. assumption. assumption.
Qed.

Lemma subgrouprightmember {G : Type}{g : Group G}{r : Restrict G}{h : Subgroup G} : forall (a b : G),
  member b -> member a <-> member(a ** b).
Proof.
  intros; split; intros.
  * apply closure with a b in H. assumption. assumption.
  * apply inverse in H. apply closure with (a ** b) (inv b) in H. rewrite <- associativity in H.
    rewrite rightinverse in H. rewrite rightidentity in H. assumption. assumption.
Qed.

(*the below proof is difficult, not sure how to complete it. *)
Theorem fundamentaltheoremofcyclicgroups {G : Type}{g : Group G}{c : CyclicGroup G}{r : Restrict G}{h : Subgroup G} :
  exists (a : G), member a /\ forall (h : G), member h -> exists (n : nat), h = opexponent a n.
Proof.
  remember generator as A. destruct A. eexists. split.
  * Abort. 
  (*exists x.  intros. destruct. split. *)

(* Cosets *)

Class LeftCosetRestrict (G : Type) : Type :=
{
  lcosetmember : G -> Prop
}.

Class RightCosetRestrict (G : Type) : Type :=
{
  rcosetmember : G -> Prop
}.

(*Not all cosets are groups, so we do not give it the subgroup annotation*)
Class leftcoset {G: Type}{g : Group G}(r : Restrict G){c : LeftCosetRestrict G}(a : G):=
{
  inleftcoset : forall (h : G), member h ->  lcosetmember (a ** h)
}.

Class rightcoset {G: Type}{g : Group G}(r : Restrict G){c : RightCosetRestrict G}(a : G):=
{
  inrightcoset : forall (h : G), member h ->  rcosetmember (h ** a)
}.

Definition leftrightcosetequalfora {G : Type}{g : Group G}{r : Restrict G}(h : Subgroup G)(a : G)
      {l : LeftCosetRestrict G}{r : RightCosetRestrict G} : Prop := 
  forall (s : G), member s -> (lcosetmember (a ** s) <-> rcosetmember (s ** a)).

Definition leftrightcosetsequal {G : Type}{g : Group G}{r : Restrict G}(h : Subgroup G)
{l : LeftCosetRestrict G}{r : RightCosetRestrict G} : Prop :=
  forall (a : G), leftrightcosetequalfora h a.

Definition leftcosetrelation {G : Type}{g : Group G}{r : Restrict G}
(a : G)(b : G) : Prop :=
  member ((inv a) ** b).

Definition rightcosetrelation {G : Type}{g : Group G}{r : Restrict G}
(a : G)(b : G) : Prop :=
  member (a ** (inv b)).

Definition isequivalencerelation {G : Type}(f : G -> G -> Prop): Prop :=
  forall (a b c : G), f a a /\ ((f a b) <-> (f b a)) /\ ((f a b) -> (f b c) -> (f a c)).

Theorem cosetrelationisequivrelation {G : Type}{g : Group G}{r : Restrict G}{h : Subgroup G} : 
 isequivalencerelation leftcosetrelation /\ isequivalencerelation rightcosetrelation.
Proof.
  unfold isequivalencerelation. split; split.
  * unfold leftcosetrelation. rewrite leftinverse. apply identityinsubgroup. reflexivity.
  * split.
    - split; unfold leftcosetrelation; intros; apply inverse in H;
      rewrite inversedistribution in H; rewrite inverseinverse in H;
      assumption.
    - unfold leftcosetrelation; repeat intros. 
      apply closure with (inv a ** b) (inv b ** c) in H.
      repeat rewrite <- associativity in H.
      assert (A: b ** (inv b ** c) = (b ** inv b) ** c).
      { rewrite <- associativity. reflexivity. }
        rewrite A in H. rewrite rightinverse in H.
        rewrite leftidentity in H. assumption.
        assumption.
  * unfold rightcosetrelation. rewrite rightinverse. apply identityinsubgroup. reflexivity.
  *  split.
    - split; unfold rightcosetrelation; intros; apply inverse in H;
      rewrite inversedistribution in H; rewrite inverseinverse in H;
      assumption.
    - unfold rightcosetrelation; repeat intros. 
      apply closure with (a ** inv b) (b ** inv c) in H.
      repeat rewrite <- associativity in H.
      assert (A: inv b ** (b ** inv c) = (inv b ** b) ** inv c).
      { rewrite <- associativity. reflexivity. }
        rewrite A in H. rewrite leftinverse in H.
        rewrite leftidentity in H. assumption.
        assumption.
Qed.

Class LeftCosetEquivalenceClass {G: Type}{g : Group G}{r : Restrict G}{c : LeftCosetRestrict G}(a : G):=
{
  inleftcosetequivalenceclass (b : G) : leftcosetrelation a b
}.

Class RightCosetEquivalenceClass {G: Type}{g : Group G}{r : Restrict G}{c : RightCosetRestrict G}(a : G):=
{
  inrightcosetequivalenceclass (b : G) : rightcosetrelation a b
}.

Class LeftCosets (G: Type){g : Group G}{r : Restrict G}{c : LeftCosetRestrict G}:=
{
  aleftcoset (a : G) : LeftCosetEquivalenceClass a
}.

Class FiniteLeftCosets (G: Type){g : Group G}{r : Restrict G}{c : LeftCosetRestrict G}{f : Finite G} : Type := {}.

Definition leftcosetsfinitecardinality {G : Type}{g : Group G}{r : Restrict G}{c : LeftCosetRestrict G}{f : Finite G}
{flc : FiniteLeftCosets G} : nat :=
  length(elements).

Class RightCosets (G: Type){g : Group G}{r : Restrict G}{c : RightCosetRestrict G}:=
{
  arightcoset (a : G) : RightCosetEquivalenceClass a
}.

Class FiniteRightCosets (G: Type){g : Group G}{r : Restrict G}{c : RightCosetRestrict G}{f : Finite G} : Type := {}.

Definition rightcosetsfinitecardinality {G : Type}{g : Group G}{r : Restrict G}{c : RightCosetRestrict G}{f : Finite G}
{frc : FiniteRightCosets G} : nat :=
  length(elements).

Definition isbijective {A : Type}{B : Type}(f : A -> B) :=
  (forall (b1 b2 : B)(a1 a2 : A), b1 = f a1 -> b2 = f a2 -> b1 = b2 -> a1 = a2) 
  /\ (forall (b : B), exists (a : A), f a = b).

(* The (a : G) is the representative of the coset aH, while h is intended to be any element
    of the subgroup. The proof of Lagrange's theorem uses the bijectivity of this function to 
    show that for any coset aH, aH has the same number of elements as H.*)
Definition lagrangemapping {G : Type}{g : Group G}{r : Restrict G} 
{s : Subgroup G}{f: Finite G}{fg : FiniteGroup G}{sf : FiniteSubgroup G}(a : G) : G -> G := fun h => a ** h.
    
Theorem partoflagrange {G : Type}{g : Group G}{r : Restrict G} 
{s : Subgroup G}{f: Finite G}{fg : FiniteGroup G}{sf : FiniteSubgroup G}
(a : G): isbijective (lagrangemapping a).
Proof.
  unfold isbijective. unfold lagrangemapping. split; intros.
  * rewrite H1 in H. rewrite H0 in H. apply leftcancellation in H.
    symmetry. assumption.
  * exists (inv a ** b). rewrite associativity. rewrite rightinverse.
    rewrite leftidentity. reflexivity.
Qed.

(*The above theorem is intended to show that "Every coset of a subgroup of H
  of a group G has the same number of elements as H", a statement which once established,
  Lagrange's theorem follows almost immediately from,
  as shown in Theorem 10.10 in Fraleigh,
  "A First Course in Abstract Algebra". However, my implementation has a couple of issues,
  namely that my Lagrange mapping goes from G -> G and does not reflect the fact that
  the mapping should go H -> G in the informal proof. Additionally, I have been unsuccessful
  in thinking of a way to count the number of items in a left coset equivalence class,
  and I also haven't shown a way to count the number of left coset equivalence classes.
  From the above theorem, when stated correctly, Lagrange's theorem is a direct result
  of the fact that the order of the group must be equal to the number of cosets times the number of 
  items in each coset - the above theorem proving that the number of items in each coset
  must be the same as the number of items in the subgroup H from which the cosets are generated from,
  gives the result of Lagrange's theorem: the order of H divides the order of G.
  *)

Theorem Lagrange {G : Type}{g : Group G}{r : Restrict G} 
{s : Subgroup G}{f: Finite G}{fg : FiniteGroup G}{sf : FiniteSubgroup G}
: exists (n : nat), n * subgroupfiniteorder = finiteorder.
Proof.
Abort.

(*Factor/Quotient Groups: Expansion *)
(*Class QuotientGroup (G : Type){g : Group G}{r : Restrict G}{h : Subgroup G}{n : NormalSubgroup G} : Type :=
{

}
*)

