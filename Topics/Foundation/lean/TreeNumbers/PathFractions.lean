module

public import TreeNumbers.PathIntegers

@[expose] public section

/-!
# Auxiliary fraction data `(TreeZ, positive TreeN)`

This is an *auxiliary* proof device only: raw fraction data consisting of a tree integer
numerator and a strictly positive path-count denominator, with the cross-multiplication
relation.  The rational field itself (`TreeQ`) is a quotient of triple-path configurations;
the operations here are used to *construct new triple-path witnesses*.
All symbols refer to `TreeZ`/`TreeN` operations constructed in this project.
-/

open TreeN (PathLT zero_lt_succ mul_pos succ succ_ne_zero eq_zero_of_add_eq_zero_right)
open TreeZ CSR CRing

/-- Raw fraction data: numerator in `TreeZ`, strictly positive denominator in `TreeN`. -/
structure Frac where
  num : TreeZ
  den : TreeN
  pos : PathLT TreeN.zero den

namespace Frac

theorem ext {f g : Frac} (h1 : f.num = g.num) (h2 : f.den = g.den) : f = g := by
  cases f
  cases g
  cases h1
  cases h2
  rfl

/-- The denominator embedded in `TreeZ`. -/
abbrev dz (f : Frac) : TreeZ := ofN f.den

theorem dz_ne (f : Frac) : f.dz ≠ 𝟘 := ofN_ne_zero f.pos

/-- Cross-multiplication relation. -/
def Eqv (f g : Frac) : Prop := f.num * g.dz = g.num * f.dz

instance (f g : Frac) : Decidable (Eqv f g) := TreeZ.decEq _ _

theorem eqv_refl (f : Frac) : Eqv f f := rfl

theorem eqv_symm {f g : Frac} (h : Eqv f g) : Eqv g f := h.symm

theorem eqv_trans {f g h : Frac} (h1 : Eqv f g) (h2 : Eqv g h) : Eqv f h := by
  unfold Eqv at *
  apply TreeZ.mul_right_cancel (dz_ne g)
  rw [mul_right_comm, h1, mul_right_comm, h2, mul_right_comm]

theorem eqv_of_eq {f g : Frac} (h : f = g) : Eqv f g := by
  rw [h]
  exact eqv_refl g

/-! ## Operations (derived cross formulas) -/

def zero : Frac := ⟨𝟘, TreeN.one, zero_lt_succ TreeN.zero⟩
def one : Frac := ⟨𝟙, TreeN.one, zero_lt_succ TreeN.zero⟩

/-- `(a,d) + (c,e) := (a·e + c·d, d·e)`. -/
def add (f g : Frac) : Frac := ⟨f.num * g.dz + g.num * f.dz, f.den * g.den, mul_pos f.pos g.pos⟩

def neg (f : Frac) : Frac := ⟨-f.num, f.den, f.pos⟩

/-- `(a,d) · (c,e) := (a·c, d·e)`. -/
def mul (f g : Frac) : Frac := ⟨f.num * g.num, f.den * g.den, mul_pos f.pos g.pos⟩

/-- Inversion via the constructive sign decision on the numerator; `inv 0 = 0`. -/
def inv (f : Frac) : Frac :=
  match sign f.num with
  | Sign.zero _ => zero
  | Sign.pos n _ => ⟨f.dz, succ n, zero_lt_succ n⟩
  | Sign.neg n _ => ⟨-f.dz, succ n, zero_lt_succ n⟩

/-- Embedding of path counts as fractions with denominator one. -/
def ofTreeN (n : TreeN) : Frac := ⟨ofN n, TreeN.one, zero_lt_succ TreeN.zero⟩

theorem dz_mul (f g : Frac) : (mul f g).dz = f.dz * g.dz := ofN_mul _ _

theorem dz_add (f g : Frac) : (add f g).dz = f.dz * g.dz := ofN_mul _ _

/-! ## Compatibility with the relation -/

theorem add_comm (f g : Frac) : add f g = add g f :=
  ext (CSR.add_comm _ _) (TreeN.mul_comm _ _)

theorem mul_comm (f g : Frac) : mul f g = mul g f :=
  ext (CSR.mul_comm _ _) (TreeN.mul_comm _ _)

theorem add_resp_left {f f' : Frac} (g : Frac) (h : Eqv f f') : Eqv (add f g) (add f' g) := by
  unfold Eqv at *
  rw [dz_add, dz_add]
  show (f.num * g.dz + g.num * f.dz) * (f'.dz * g.dz)
    = (f'.num * g.dz + g.num * f'.dz) * (f.dz * g.dz)
  rw [right_distrib, right_distrib, mul_mul_mul_comm f.num, mul_mul_mul_comm f'.num, h,
    mul_assoc g.num f.dz, mul_left_comm f.dz f'.dz, mul_assoc g.num f'.dz]

theorem add_resp {f f' g g' : Frac} (h1 : Eqv f f') (h2 : Eqv g g') :
    Eqv (add f g) (add f' g') := by
  apply eqv_trans (add_resp_left g h1)
  rw [add_comm f', add_comm f']
  exact add_resp_left f' h2

theorem mul_resp_left {f f' : Frac} (g : Frac) (h : Eqv f f') : Eqv (mul f g) (mul f' g) := by
  unfold Eqv at *
  rw [dz_mul, dz_mul]
  show f.num * g.num * (f'.dz * g.dz) = f'.num * g.num * (f.dz * g.dz)
  rw [mul_mul_mul_comm, mul_mul_mul_comm f'.num, h]

theorem mul_resp {f f' g g' : Frac} (h1 : Eqv f f') (h2 : Eqv g g') :
    Eqv (mul f g) (mul f' g') := by
  apply eqv_trans (mul_resp_left g h1)
  rw [mul_comm f', mul_comm f']
  exact mul_resp_left f' h2

theorem neg_resp {f f' : Frac} (h : Eqv f f') : Eqv (neg f) (neg f') := by
  unfold Eqv at *
  show -f.num * f'.dz = -f'.num * f.dz
  rw [neg_mul, neg_mul, h]

/-- `ofN m = -(ofN n)` forces both to vanish. -/
theorem ofN_eq_neg_ofN {m n : TreeN} (h : ofN m = -ofN n) : n = TreeN.zero := by
  have h2 : ofN (m + n) = 𝟘 := by
    rw [ofN_add, h, neg_add_cancel]
  exact eq_zero_of_add_eq_zero_right (ofN_injective h2)

theorem pos_ne_neg {n n' : TreeN} {D D' : TreeZ} (hD : D ≠ 𝟘)
    (hD' : NonNeg D') (hD'' : NonNeg D) (h : ofN (succ n) * D' = -ofN (succ n') * D) : False := by
  rw [nonNeg_eq hD', nonNeg_eq hD'', ← ofN_mul, neg_mul, ← ofN_mul] at h
  have e := ofN_eq_neg_ofN h
  cases TreeN.mul_eq_zero e with
  | inl e1 => exact succ_ne_zero n' e1
  | inr e2 =>
    apply hD
    rw [nonNeg_eq hD'', e2]
    rfl

theorem inv_resp {f f' : Frac} (h : Eqv f f') : Eqv (inv f) (inv f') := by
  unfold Eqv at h
  unfold inv
  have hd := f.dz_ne
  have hd' := f'.dz_ne
  have nd : NonNeg f.dz := nonNeg_ofN _
  have nd' : NonNeg f'.dz := nonNeg_ofN _
  match sign f.num, sign f'.num with
  | Sign.zero _, Sign.zero _ => exact eqv_refl _
  | Sign.zero e, Sign.pos n' e' =>
    rw [e, e', zero_mul] at h
    exact absurd h.symm (mul_ne_zero (ofN_ne_zero (zero_lt_succ n')) hd)
  | Sign.zero e, Sign.neg n' e' =>
    rw [e, e', zero_mul] at h
    exact absurd h.symm (mul_ne_zero (fun x => ofN_ne_zero (zero_lt_succ n')
      (by rw [← neg_neg (ofN (succ n')), x, neg_zero])) hd)
  | Sign.pos n e, Sign.zero e' =>
    rw [e, e', zero_mul] at h
    exact absurd h (mul_ne_zero (ofN_ne_zero (zero_lt_succ n)) hd')
  | Sign.neg n e, Sign.zero e' =>
    rw [e, e', zero_mul] at h
    exact absurd h (mul_ne_zero (fun x => ofN_ne_zero (zero_lt_succ n)
      (by rw [← neg_neg (ofN (succ n)), x, neg_zero])) hd')
  | Sign.pos n e, Sign.pos n' e' =>
    rw [e, e'] at h
    show f.dz * ofN (succ n') = f'.dz * ofN (succ n)
    rw [CSR.mul_comm f.dz, ← h, CSR.mul_comm]
  | Sign.neg n e, Sign.neg n' e' =>
    rw [e, e', neg_mul, neg_mul] at h
    have h' : ofN (succ n) * f'.dz = ofN (succ n') * f.dz := by
      rw [← neg_neg (ofN (succ n) * f'.dz), h, neg_neg]
    show -f.dz * ofN (succ n') = -f'.dz * ofN (succ n)
    rw [neg_mul, neg_mul, CSR.mul_comm f.dz, ← h', CSR.mul_comm]
  | Sign.pos n e, Sign.neg n' e' =>
    rw [e, e'] at h
    exact (pos_ne_neg hd nd' nd h).elim
  | Sign.neg n e, Sign.pos n' e' =>
    rw [e, e'] at h
    exact (pos_ne_neg hd' nd nd' h.symm).elim

/-! ## Field laws on raw fraction data (literally, or up to the relation) -/

theorem add_assoc (f g h : Frac) : add (add f g) h = add f (add g h) := by
  apply ext
  · show (f.num * g.dz + g.num * f.dz) * h.dz + h.num * (add f g).dz
      = f.num * (add g h).dz + (g.num * h.dz + h.num * g.dz) * f.dz
    rw [dz_add, dz_add, right_distrib, right_distrib, CSR.add_assoc, mul_assoc, mul_assoc,
      mul_assoc, mul_assoc, CSR.mul_comm f.dz h.dz, CSR.mul_comm f.dz g.dz]
  · exact TreeN.mul_assoc _ _ _

theorem zero_add (f : Frac) : add zero f = f := by
  apply ext
  · show 𝟘 * f.dz + f.num * ofN TreeN.one = f.num
    rw [zero_mul, CSR.zero_add, ofN_one, CSR.mul_one]
  · exact TreeN.one_mul _

theorem neg_add_cancel (f : Frac) : Eqv (add (neg f) f) zero := by
  unfold Eqv
  show (-f.num * f.dz + f.num * f.dz) * ofN TreeN.one = 𝟘 * (add (neg f) f).dz
  rw [CRing.neg_mul, CRing.neg_add_cancel, zero_mul, zero_mul]

theorem mul_assoc' (f g h : Frac) : mul (mul f g) h = mul f (mul g h) :=
  ext (CSR.mul_assoc _ _ _) (TreeN.mul_assoc _ _ _)

theorem one_mul (f : Frac) : mul one f = f :=
  ext (CSR.one_mul _) (TreeN.one_mul _)

theorem left_distrib (f g h : Frac) : Eqv (mul f (add g h)) (add (mul f g) (mul f h)) := by
  unfold Eqv
  rw [dz_add, dz_mul, dz_mul, dz_mul, dz_add]
  show f.num * (g.num * h.dz + h.num * g.dz) * (f.dz * g.dz * (f.dz * h.dz))
    = (f.num * g.num * (mul f h).dz + f.num * h.num * (mul f g).dz) * (f.dz * (g.dz * h.dz))
  rw [dz_mul, dz_mul]
  have e : f.num * g.num * (f.dz * h.dz) + f.num * h.num * (f.dz * g.dz)
      = f.num * (g.num * h.dz + h.num * g.dz) * f.dz := by
    have t1 : f.num * g.num * (f.dz * h.dz) = f.num * (g.num * h.dz) * f.dz := by
      rw [mul_assoc f.num g.num, mul_assoc f.num (g.num * h.dz), mul_assoc g.num h.dz,
        CSR.mul_comm h.dz f.dz]
    have t2 : f.num * h.num * (f.dz * g.dz) = f.num * (h.num * g.dz) * f.dz := by
      rw [mul_assoc f.num h.num, mul_assoc f.num (h.num * g.dz), mul_assoc h.num g.dz,
        CSR.mul_comm g.dz f.dz]
    rw [CSR.left_distrib, right_distrib, t1, t2]
  rw [e, mul_assoc _ f.dz, mul_mul_mul_comm f.dz g.dz f.dz h.dz, mul_assoc f.dz f.dz]

theorem zero_ne_one : ¬ Eqv zero one := by
  intro h
  unfold Eqv at h
  have h' : (𝟘 : TreeZ) * ofN TreeN.one = 𝟙 * ofN TreeN.one := h
  rw [zero_mul, ofN_one, CSR.one_mul] at h'
  exact TreeZ.zero_ne_one h'

theorem num_eq_zero_of_eqv_zero {f : Frac} (h : Eqv f zero) : f.num = 𝟘 := by
  unfold Eqv at h
  have h' : f.num * ofN TreeN.one = 𝟘 * f.dz := h
  rw [zero_mul, ofN_one, CSR.mul_one] at h'
  exact h'

theorem eqv_zero_of_num_eq_zero {f : Frac} (h : f.num = 𝟘) : Eqv f zero := by
  unfold Eqv
  show f.num * ofN TreeN.one = 𝟘 * f.dz
  rw [h, zero_mul, zero_mul]

theorem mul_inv_cancel {f : Frac} (h : f.num ≠ 𝟘) : Eqv (mul f (inv f)) one := by
  unfold Eqv inv
  match sign f.num with
  | Sign.zero e => exact absurd e h
  | Sign.pos n e =>
    show f.num * f.dz * ofN TreeN.one = 𝟙 * ofN (f.den * succ n)
    rw [e, ofN_one, CSR.mul_one, CSR.one_mul, ofN_mul, CSR.mul_comm]
  | Sign.neg n e =>
    show f.num * -f.dz * ofN TreeN.one = 𝟙 * ofN (f.den * succ n)
    rw [e, ofN_one, CSR.mul_one, CSR.one_mul, neg_mul_neg, ofN_mul, CSR.mul_comm]

theorem inv_of_num_zero {f : Frac} (h : f.num = 𝟘) : inv f = zero := by
  unfold inv
  match sign f.num with
  | Sign.zero _ => rfl
  | Sign.pos n e => exact absurd (h.symm.trans e) (fun x => ofN_ne_zero (zero_lt_succ n) x.symm)
  | Sign.neg n e =>
    exact absurd (h.symm.trans e) (fun x => ofN_ne_zero (zero_lt_succ n)
      (by rw [← neg_neg (ofN (succ n)), ← x, neg_zero]))

theorem ofTreeN_add (m n : TreeN) : Eqv (ofTreeN (m + n)) (add (ofTreeN m) (ofTreeN n)) := by
  apply eqv_of_eq
  apply ext
  · show ofN (m + n) = ofN m * ofN TreeN.one + ofN n * ofN TreeN.one
    rw [ofN_one, CSR.mul_one, CSR.mul_one, ofN_add]
  · rfl

theorem ofTreeN_succ_ne_zero (n : TreeN) : ¬ Eqv (ofTreeN (succ n)) zero := by
  intro h
  exact ofN_ne_zero (zero_lt_succ n) (num_eq_zero_of_eqv_zero h)

end Frac
end
