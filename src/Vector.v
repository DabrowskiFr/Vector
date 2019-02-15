(************************************************************************)
(* Copyright 2018 Frédéric Dabrowski                                    *)
(* 
    This program is free software:: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.
    Foobar is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    You should have received a copy of the GNU General Public License
    along with Foobar.  If not, see <https://www.gnu.org/licenses/>.    *)
(************************************************************************)

Require Import Structure.Monad.
Require Import Structure.Functor.
Require Import List.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∀ x .. y ']' , P") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃ x .. y ']' , P") : type_scope.

Open Scope functor_scope.

Module Type Process.
  Parameter p : nat.
End Process.

Module Type Vector (Import P : Process).

  (** * Definitions *)
  
  Parameter t : Type -> Type.

  Parameter make : ∀ (A : Type), (nat -> A) -> (t A).
  Arguments make [A] _.

  Parameter vempty : ∀ A : Type, p = 0 -> t A.
  
  Parameter π : ∀ (A : Type), nat -> (t A) -> option A.
  Arguments π [A ] _ _.

  Declare Instance v_functor : Functor t.
  
  Declare Instance v_applicative : Applicative t v_functor.
       
  Parameter erase : ∀ (A : Type),
      t (option A) -> option (t A).
  Arguments erase [_] _.

  (** * Properties *)
  
  Parameter π_prop : ∀ (A : Type) (v : t A) (i : nat),
      (∃ x, π i v = Some x) <-> i < p.
  
  Parameter π_fmap : ∀ (A B : Type) (f : A -> B),
    forall i v, π i (fmap f v) = pure f <*> π i v.
  
  Parameter π_make : ∀ (A : Type) (f : nat -> A),
    forall i, i < p -> π i (make f) = pure (f i).
  
  Parameter π_pure : ∀ (A : Type),
    forall i (x : A), i < p -> π i (pure x) = pure x.
  
  Parameter π_ap : ∀ (A B : Type) (v1 : t (A -> B)) (v2 : t A),
    forall i, π i (v1 <*> v2) = (π i v1) <*> (π i v2).

  Parameter erase_prop :
    ∀ A  (v : t (option A)) (v' : t A),
      erase v = pure v' <-> v = fmap pure v'.
  
  Parameter vect_eq_dec : ∀ (A : Type),
      (∀ (x y:A), x=y \/ x<>y) -> forall (v1 v2 : t A), v1=v2 \/ v1<>v2.
  
  Parameter vect_extensionality : forall (A : Type) (v v' : t A),
      (∀ i, i < p -> π i v = π i v') -> v = v'.
  
  Hint Resolve π_ap π_fmap π_make π_pure : projection.

  Hint Rewrite π_ap π_fmap π_make π_pure : projection.
  
End Vector.