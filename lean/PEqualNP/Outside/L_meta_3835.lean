import Mathlib
import PEqualNP.Defs

-- Peeling off the first gate of a fan-in-two circuit: the rest of the circuit, run on
-- the inputs followed by the value of that gate, computes the same output; and the
-- value of the first gate is a constant, a literal, or an AND or OR of two inputs.
namespace PEqualNP.Outside.L_meta_3835

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first gate only sees the inputs.
theorem eval_cons (g : Gate) (gs : List Gate) (o : ℕ) (xs : List Bool) :
    (Circuit.mk (g :: gs) o).eval xs
      = (Circuit.mk gs o).eval (xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)]) :=
  rfl

-- Every wire index reads like some index at most n on inputs of length n.
theorem idx (n a : ℕ) : ∃ i : Fin (n + 1), ∀ xs : List Bool, xs.length = n →
    xs.getD a false = xs.getD i.val false := by
  by_cases h : a < n
  · exact ⟨⟨a, by omega⟩, fun xs _ => rfl⟩
  · refine ⟨⟨n, by omega⟩, fun xs hx => ?_⟩
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp [hx])]

theorem high (n a : ℕ) (h : n ≤ a) (xs : List Bool) (hx : xs.length = n) :
    xs.getD a false = false :=
  List.getD_eq_default _ _ (by omega)

-- The two shapes of the claim, for a function of the inputs.
def Unary (n : ℕ) (f : List Bool → Bool) : Prop :=
  ∃ (i : Fin (n + 1)) (flip : Bool), ∀ xs : List Bool, xs.length = n →
    f xs = (flip != xs.getD i.val false)

def Binary (n : ℕ) (f : List Bool → Bool) : Prop :=
  ∃ (i j : Fin n) (disj : Bool), i < j ∧ ∀ xs : List Bool, xs.length = n →
    f xs = (if disj then xs.getD i.val false || xs.getD j.val false
      else xs.getD i.val false && xs.getD j.val false)

theorem unary_const (n : ℕ) (c : Bool) (f : List Bool → Bool)
    (hf : ∀ xs : List Bool, xs.length = n → f xs = c) : Unary n f := by
  refine ⟨⟨n, by omega⟩, c, fun xs hx => ?_⟩
  rw [hf xs hx, high n n le_rfl xs hx]
  cases c <;> rfl

theorem unary_lit (n a : ℕ) (flip : Bool) (f : List Bool → Bool)
    (hf : ∀ xs : List Bool, xs.length = n → f xs = (flip != xs.getD a false)) : Unary n f := by
  obtain ⟨i, hi⟩ := idx n a
  exact ⟨i, flip, fun xs hx => by rw [hf xs hx, hi xs hx]⟩

-- AND or OR of two wire indices.
theorem two (n a b : ℕ) (disj : Bool) (f : List Bool → Bool)
    (hf : ∀ xs : List Bool, xs.length = n → f xs =
      (if disj then xs.getD a false || xs.getD b false
        else xs.getD a false && xs.getD b false)) :
    Unary n f ∨ Binary n f := by
  by_cases ha : a < n
  · by_cases hb : b < n
    · rcases lt_trichotomy a b with hab | hab | hab
      · exact Or.inr ⟨⟨a, ha⟩, ⟨b, hb⟩, disj, hab, hf⟩
      · subst hab
        refine Or.inl (unary_lit n a false f fun xs hx => ?_)
        rw [hf xs hx]
        cases disj <;> cases xs.getD a false <;> rfl
      · refine Or.inr ⟨⟨b, hb⟩, ⟨a, ha⟩, disj, hab, fun xs hx => ?_⟩
        rw [hf xs hx]
        cases disj <;> cases xs.getD a false <;> cases xs.getD b false <;> rfl
    · cases disj
      · refine Or.inl (unary_const n false f fun xs hx => ?_)
        rw [hf xs hx, high n b (by omega) xs hx]
        cases xs.getD a false <;> rfl
      · refine Or.inl (unary_lit n a false f fun xs hx => ?_)
        rw [hf xs hx, high n b (by omega) xs hx]
        cases xs.getD a false <;> rfl
  · cases disj
    · refine Or.inl (unary_const n false f fun xs hx => ?_)
      rw [hf xs hx, high n a (by omega) xs hx]
      cases xs.getD b false <;> rfl
    · refine Or.inl (unary_lit n b false f fun xs hx => ?_)
      rw [hf xs hx, high n a (by omega) xs hx]
      cases xs.getD b false <;> rfl

-- The value of a gate of the basis with at most two inputs, as a function of the inputs.
theorem gate_class (n : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    Unary n (fun xs => g.op.eval (g.inputs.map fun k => xs.getD k false)) ∨
    Binary n (fun xs => g.op.eval (g.inputs.map fun k => xs.getD k false)) := by
  obtain ⟨op, inputs⟩ := g
  rcases hop with h | h | h
  · have hop : op = GateOp.and := h
    subst hop
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact Or.inl (unary_const n true _ fun xs _ => by simp [GateOp.eval])
    · exact Or.inl (unary_lit n a false _ fun xs _ => by simp [GateOp.eval])
    · exact two n a b false _ fun xs _ => by simp [GateOp.eval]
    · simp at hlen
  · have hop : op = GateOp.or := h
    subst hop
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact Or.inl (unary_const n false _ fun xs _ => by simp [GateOp.eval])
    · exact Or.inl (unary_lit n a false _ fun xs _ => by simp [GateOp.eval])
    · exact two n a b true _ fun xs _ => by simp [GateOp.eval]
    · simp at hlen
  · have hop : op = GateOp.not := h
    subst hop
    rcases inputs with _ | ⟨a, l⟩
    · exact Or.inl (unary_const n true _ fun xs _ => by simp [GateOp.eval])
    · exact Or.inl (unary_lit n a true _ fun xs _ => by simp [GateOp.eval])

end PEqualNP.Outside.L_meta_3835

theorem PEqualNP.Outside.L_meta_3835 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (0 : ℕ) < x2.size → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size + (1 : ℕ) = x2.size ∧ ((∃ (x6 : Fin (x1 + (1 : ℕ))) (x7 : Bool), ∀ (x8 : List Bool), x8.length = x1 → x2.eval x8 = x5.eval (x8 ++ [x7 != x8.getD (↑x6) Bool.false])) ∨ ∃ (x6 : Fin x1) (x7 : Fin x1) (x8 : Bool), x6 < x7 ∧ ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = x5.eval (x9 ++ [if x8 = Bool.true then x9.getD (↑x6) Bool.false || x9.getD (↑x7) Bool.false else x9.getD (↑x6) Bool.false && x9.getD (↑x7) Bool.false])) := by
  intro n0 C0 hfan hpos
  obtain ⟨gates0, o0⟩ := C0
  cases gates0 with
  | nil => exact absurd hpos (by simp [PEqualNP.CircuitLowerBounds.Circuit.size])
  | cons g0 gs0 =>
    refine ⟨⟨gs0, o0⟩, fun g hg => hfan g (List.mem_cons_of_mem _ hg), rfl, ?_⟩
    obtain ⟨hop, hlen⟩ := hfan g0 (List.mem_cons_self ..)
    rcases PEqualNP.Outside.L_meta_3835.gate_class n0 g0 hop hlen with
      ⟨i0, flip0, h0⟩ | ⟨i0, j0, disj0, hij0, h0⟩
    · refine Or.inl ⟨i0, flip0, fun xs hx => ?_⟩
      have h1 := h0 xs hx
      simp only at h1
      rw [PEqualNP.Outside.L_meta_3835.eval_cons, h1]
    · refine Or.inr ⟨i0, j0, disj0, hij0, fun xs hx => ?_⟩
      have h1 := h0 xs hx
      simp only at h1
      rw [PEqualNP.Outside.L_meta_3835.eval_cons, h1]
