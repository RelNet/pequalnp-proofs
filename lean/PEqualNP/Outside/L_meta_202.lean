import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_202

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs rest : List Gate) (w : List Bool) :
    run (gs ++ rest) w = run rest (run gs w) := by
  simp [run, List.foldl_append]

lemma run_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]
    simp

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht]
  simp [hl]

lemma run_initial (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

lemma run_or (w : List Bool) (a h : ℕ) :
    run [⟨GateOp.or, [a, h]⟩] w =
      w ++ [w.getD a false || w.getD h false] := by
  simp [run, GateOp.eval]

lemma preserves (n j a h : ℕ) (C : Circuit)
    (hFan : FanInTwo C)
    (hgate : C.gates[j]? = some ⟨GateOp.or, [a, h]⟩)
    (hbound : h < n + j)
    (hImp : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      circuitFun n C x = true) :
    FanInTwo { gates := C.gates.set j ⟨GateOp.or, [a]⟩ ++
      [⟨GateOp.or, [C.output, h]⟩], output := n + C.size } ∧
    circuitFun n { gates := C.gates.set j ⟨GateOp.or, [a]⟩ ++
      [⟨GateOp.or, [C.output, h]⟩], output := n + C.size } = circuitFun n C := by
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_or_eq_of_mem_set hg with hg | rfl
      · exact hFan g hg
      · simp
    · have he : g = (⟨GateOp.or, [C.output, h]⟩ : Gate) := List.mem_singleton.mp hg
      subst g
      simp
  · funext x
    obtain ⟨hj, heq⟩ := List.getElem?_eq_some_iff.1 hgate
    have hsplit : C.gates = C.gates.take j ++
        (⟨GateOp.or, [a, h]⟩ : Gate) :: C.gates.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop (j + 1) C.gates]
      rw [List.take_succ_eq_append_getElem hj, heq, List.append_assoc]
      rfl
    have hset : C.gates.set j ⟨GateOp.or, [a]⟩ = C.gates.take j ++
        (⟨GateOp.or, [a]⟩ : Gate) :: C.gates.drop (j + 1) := by
      rw [List.set_eq_take_append_cons_drop, if_pos hj]
    let w := run (C.gates.take j) (List.ofFn x)
    let v := run (C.gates.set j ⟨GateOp.or, [a]⟩) (List.ofFn x)
    have hwlen : w.length = n + j := by
      simp [w, run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hvlen : v.length = n + C.size := by
      simp [v, run_length, Circuit.size]
    have hh : h < w.length := by omega
    have hvh : v.getD h false = w.getD h false := by
      change (run (C.gates.set j ⟨GateOp.or, [a]⟩) (List.ofFn x)).getD h false = _
      rw [hset, run_append]
      exact run_initial _ w h hh
    have hCh : (C.wires (List.ofFn x)).getD h false = w.getD h false := by
      change (run C.gates (List.ofFn x)).getD h false = _
      rw [hsplit, run_append]
      exact run_initial _ w h hh
    have hnew : circuitFun n
        { gates := C.gates.set j ⟨GateOp.or, [a]⟩ ++ [⟨GateOp.or, [C.output, h]⟩],
          output := n + C.size } x =
        (v.getD C.output false || v.getD h false) := by
      change (run (C.gates.set j ⟨GateOp.or, [a]⟩ ++
        [⟨GateOp.or, [C.output, h]⟩]) (List.ofFn x)).getD (n + C.size) false = _
      rw [run_append, run_or]
      change (v ++ [v.getD C.output false || v.getD h false]).getD (n + C.size) false = _
      rw [← hvlen, getD_last]
    cases hval : w.getD h false with
    | false =>
      have hsame : v = C.wires (List.ofFn x) := by
        change run (C.gates.set j ⟨GateOp.or, [a]⟩) (List.ofFn x) =
          run C.gates (List.ofFn x)
        conv_lhs => rw [hset, run_append]
        conv_rhs => rw [hsplit, run_append]
        change run (C.gates.drop (j + 1))
            (w ++ [GateOp.or.eval ([a].map fun i => w.getD i false)]) =
          run (C.gates.drop (j + 1))
            (w ++ [GateOp.or.eval ([a, h].map fun i => w.getD i false)])
        congr 1
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false, hval]
      rw [hnew, hvh, hval, Bool.or_false]
      change v.getD C.output false = (C.wires (List.ofFn x)).getD C.output false
      rw [hsame]
    | true =>
      have htrue : circuitFun n C x = true := hImp x (hCh.trans hval)
      rw [hnew, hvh, hval, Bool.or_true, htrue]

end PEqualNP.Outside.L_meta_202

theorem PEqualNP.Outside.L_meta_202 : ∀ (n j a h : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a, h]⟩ → h < n + j → (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true → PEqualNP.MetaComplexity.circuitFun n C x = true) → PEqualNP.MetaComplexity.FanInTwo { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } ∧ PEqualNP.MetaComplexity.circuitFun n { gates := C.gates.set j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [a]⟩ ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C.output, h]⟩], output := n + C.size } = PEqualNP.MetaComplexity.circuitFun n C := by
  exact PEqualNP.Outside.L_meta_202.preserves
