inductive Expr.Op
| add
| le

inductive Expr
| nat: Nat -> Expr
| op: Expr.Op -> Expr -> Expr -> Expr
| ite: Expr -> Expr -> Expr -> Expr
| assign: Nat -> Expr -> Expr
| deref: Nat -> Expr
| skip: Expr
| seq: Expr -> Expr -> Expr
| while: Expr -> Expr -> Expr

def Heap := Nat -> Nat

def Heap.set (h: Heap) (ℓ: Nat) (v: Nat): Heap
  := λ ℓ' => if ℓ = ℓ' then v else h ℓ'

def is_le (l r: Nat) := if l ≤ r then 1 else 0

inductive Expr.Reduces: Expr -> Heap -> Expr -> Heap -> Type
| op_plus (l r s): Reduces (op Op.add (nat l) (nat r)) s (nat (l + r)) s
| op_le (l r s): Reduces (op Op.le (nat l) (nat r)) s (nat (is_le l r)) s
| op1 {e e': Expr} {s s'} (o: Op) (r): Reduces e s e' s'
  -> Reduces (op o e r) s (op o e' r) s'
| op2 {e e' s s'} (o l): Reduces e s e' s'
  -> Reduces (op o (nat l) e) s (op o (nat l) e') s'
| deref {l s} : Reduces (deref l) s (nat (s l)) s
| assign1 {l v s} : Reduces (assign l (nat v)) s skip (s.set l v)
| assign2 {e e' s s'} (l) : Reduces e s e' s'
  -> Reduces (assign l e) s (assign l e') s'
| seq1 (e s): Reduces (seq skip e) s e s
| seq2 {e e' s s'} (e'') : Reduces e s e' s'
  -> Reduces (seq e e'') s (seq e' e'') s'
| if1 (n: Nat) (l r s): Reduces (ite (nat n.succ) l r) s l s
| if2 (l r s): Reduces (ite (nat 0) l r) s r s
| if3 {e e' s s'} (e1 e2): Reduces e s e' s'
  -> Reduces (ite e e1 e2) s (ite e' e1 e2) s'
| while (e b s):
  Reduces (Expr.while e b) s (ite e (seq b (Expr.while e b)) skip) s

theorem determinacy {e s e' s'}: Expr.Reduces e s e' s'
  -> ∀ e'' s'', Expr.Reduces e s e'' s''
  -> e' = e'' ∧ s' = s''
  := by
    intro H
    induction H with
    | op_plus =>
      intro e'' s'' I;
      cases I with
      | op_plus => simp
      | op1 o e I => cases I
      | op2 o e I => cases I
    | seq2 e2 He2 I =>
      intro e'' s'' H
      cases H with
      | seq1 => sorry
      | seq2 => sorry
    | _ => sorry
