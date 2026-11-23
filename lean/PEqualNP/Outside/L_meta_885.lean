import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_885

open PEqualNP.CircuitLowerBounds

def bits {n : ℕ} (B : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ B)

def readBit (g : Gate) (w : List Bool) := (g.inputs.map (fun i => w.getD i false)).headD false

def pushWire (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

noncomputable def freezeGate (w : List Bool) (g : Gate) : Gate := by
  classical
  exact if g.op = .not then ⟨if readBit g w then .or else .and, []⟩ else g

noncomputable def frozen : List Gate → List Bool → List Gate
  | [], _ => []
  | g :: gs, w => freezeGate w g :: frozen gs (pushWire w g)

theorem frozen_length (L : List Gate) (w : List Bool) : (frozen L w).length = L.length := by
  induction L generalizing w <;> simp [frozen, *]

theorem frozen_mono (L : List Gate) (w : List Bool)
    (ops : ∀ g ∈ L, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ frozen L w, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  induction L generalizing w with
  | nil => simp [frozen]
  | cons g gs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|tail
    · obtain ⟨h,len⟩ := ops g (by simp)
      rcases h with h|h|h <;> simp [freezeGate,h,len]
    · exact ih _ (fun z m => ops z (by simp [m])) _ tail

theorem frozen_eq (L : List Gate) (base x : List Bool)
    (agree : ∀ j g, L[j]? = some g → g.op = .not →
      readBit g ((L.take j).foldl pushWire base) = readBit g ((L.take j).foldl pushWire x)) :
    (frozen L base).foldl pushWire x = L.foldl pushWire x := by
  induction L generalizing base x with
  | nil => rfl
  | cons g gs ih =>
    have first : pushWire x (freezeGate base g) = pushWire x g := by
      by_cases h : g.op = .not
      · have a := agree 0 g (by simp) h
        simp only [List.take_zero,List.foldl_nil] at a
        simp only [freezeGate,h,ite_true,pushWire,GateOp.eval,List.map_nil]
        change _ ++ [(if readBit g base then GateOp.or else GateOp.and).eval []] =
          _ ++ [!(readBit g x)]
        rw [a]; cases readBit g x <;> rfl
      · simp [freezeGate,h]
    simp only [frozen,List.foldl_cons,first]
    apply ih
    intro j z hz hop
    exact agree (j+1) z (by simpa using hz) hop

def touched {n m : ℕ} (F : Fin m → Finset (Fin n)) (B : Finset (Fin n)) :=
  Finset.univ.filter fun i => ¬Disjoint (F i) B

theorem touch_bound {n m q : ℕ} (F : Fin m → Finset (Fin n))
    (join : ∀ p r, p ≠ r → ∃ i, p ∈ F i ∧ r ∈ F i)
    (deg : ∀ p, (Finset.univ.filter (fun i => p ∈ F i)).card = q+1)
    (B : Finset (Fin n)) : (touched F B).card ≤ B.card*q + 1 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [touched]
  | @insert p B hp ih =>
    let X := (Finset.univ : Finset (Fin m)).filter fun i => p ∈ F i
    have eq : touched F (insert p B) = X ∪ touched F B := by
      ext i
      simp [touched,X,Finset.disjoint_left]
      grind
    rw [eq,Finset.card_insert_of_notMem hp,Nat.add_mul,one_mul]
    have size : X.card = q+1 := deg p
    by_cases hb : B.Nonempty
    · obtain ⟨r,hr⟩ := hb
      obtain ⟨i,ip,ir⟩ := join p r (fun e => hp (e ▸ hr))
      have hi : i ∈ X ∩ touched F B := by
        simp [X,touched,ip,Finset.disjoint_left]
        exact ⟨r,ir,hr⟩
      have pos := Finset.card_pos.mpr ⟨i,hi⟩
      have := Finset.card_union_add_card_inter X (touched F B)
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hb]
      simpa [touched] using size.le

def support {n : ℕ} (x : Fin n → Bool) := Finset.univ.filter (fun p => x p = true)

def clamp {n : ℕ} (B : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun p => if p ∈ B then true else x p

theorem bits_union {n} (B : Finset (Fin n)) (x : Fin n → Bool) :
    bits (B ∪ support x) = clamp B x := by
  funext p
  by_cases h : p ∈ B <;> simp [bits,support,clamp,h]

def wireRead {n} (L : List Gate) (j : Fin L.length) (B : Finset (Fin n)) :=
  readBit (L.get j) ((L.take j.val).foldl pushWire (List.ofFn (bits B)))

theorem on_window {n m : ℕ} (B : Finset (Fin n)) (L : List Gate) (F : Fin m → Finset (Fin n))
    (o : Fin m → ℕ) (k : ℕ)
    (agree : ∀ (j : Fin L.length), (L.get j).op = .not → ∀ X : Finset (Fin n),
      X.card ≤ k → wireRead L j (B ∪ X) = wireRead L j B)
    (computes : ∀ i (x : Fin n → Bool), Circuit.eval ⟨L,o i⟩ (List.ofFn x) =
      decide (∃ v ∈ F i, x v = true)) :
    ∀ i (x : Fin n → Bool), (support x).card ≤ k →
      Circuit.eval ⟨frozen L (List.ofFn (bits B)),o i⟩ (List.ofFn (clamp B x)) =
      decide (∃ v ∈ F i, clamp B x v = true) := by
  intro i x hx
  rw [← computes]
  unfold Circuit.eval Circuit.wires
  change ((frozen L _).foldl pushWire _).getD _ false = (L.foldl pushWire _).getD _ false
  congr 1
  apply frozen_eq
  intro j g hg hn
  obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp hg
  subst g
  have h := agree ⟨j,bound⟩ hn (support x) hx
  unfold wireRead at h
  rw [bits_union] at h
  exact h.symm

theorem recover_budget (K a t k q m live loss : ℕ) (ht : 1 ≤ t)
    (partition : live + loss = m)
    (lost : loss ≤ (t-1)*k*q+1)
    (bound : K + a*(t*k*q+1) ≤ a*m + a*(k*q)) :
    K ≤ a*live := by
  obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  subst t
  simp only [Nat.succ_sub_one] at lost
  have step : loss + k*q ≤ (s+1)*k*q+1 := by
    rw [Nat.add_mul,Nat.add_mul,one_mul]
    omega
  have h := Nat.mul_le_mul_left a step
  rw [Nat.mul_add] at h
  rw [← partition,Nat.mul_add a live loss] at bound
  change K + a*((s+1)*k*q+1) ≤ a*live + a*loss + a*(k*q) at bound
  omega

theorem remaining {n m} (F : Fin m → Finset (Fin n)) (B : Finset (Fin n)) :
    (Finset.univ.filter (fun i => Disjoint (F i) B)).card + (touched F B).card = m := by
  classical
  simpa [touched] using Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i => Disjoint (F i) B)

theorem window {n t k : ℕ} {J : Type} [Fintype J]
    (f : J → Finset (Fin n) → Bool)
    (mono : ∀ j A B, A ⊆ B → f j A ≤ f j B) (cap : Fintype.card J ≤ t) :
    ∃ B : Finset (Fin n),
      (B.card ≤ t*k ∧ ∀ j X, f j (B ∪ X) = f j B) ∨
      (B.card ≤ (t-1)*k ∧ ∀ j (X : Finset (Fin n)), X.card ≤ k →
        f j (B ∪ X) = f j B) := by
  classical
  let off (A : Finset (Fin n)) := Finset.univ.filter (fun j => f j A = false)
  suffices walk : ∀ r ≤ t, ∀ A : Finset (Fin n), A.card ≤ (t-r)*k →
      (off A).card ≤ r → ∃ B : Finset (Fin n),
        (B.card ≤ t*k ∧ ∀ j X, f j (B ∪ X) = f j B) ∨
        (B.card ≤ (t-1)*k ∧ ∀ j (X : Finset (Fin n)), X.card ≤ k →
          f j (B ∪ X) = f j B) by
    exact walk t le_rfl ∅ (by simp) ((Finset.card_le_univ _).trans cap)
  intro r
  induction r with
  | zero =>
    intro _ A hA hOff
    refine ⟨A, Or.inl ⟨by simpa using hA, ?_⟩⟩
    intro j X
    have hempty : off A = ∅ := Finset.card_eq_zero.mp (by omega)
    have hj : f j A = true := by
      cases he : f j A with
      | false =>
        have : j ∈ off A := by simp [off, he]
        simp [hempty] at this
      | true => rfl
    have hm := mono j A (A ∪ X) Finset.subset_union_left
    rw [hj] at hm ⊢
    exact le_antisymm (by simp) hm
  | succ r ih =>
    intro hr A hA hOff
    by_cases stable : ∀ j (X : Finset (Fin n)), X.card ≤ k → f j (A ∪ X) = f j A
    · exact ⟨A, Or.inr ⟨hA.trans (Nat.mul_le_mul_right k (by omega)), stable⟩⟩
    push Not at stable
    obtain ⟨j, X, hX, hj⟩ := stable
    have hm := mono j A (A ∪ X) Finset.subset_union_left
    have flip : f j A = false ∧ f j (A ∪ X) = true := by
      cases ha : f j A <;> cases hb : f j (A ∪ X) <;> simp [ha, hb] at hm hj ⊢
      exact (by decide : ¬ (true ≤ false)) hm
    have hsub : off (A ∪ X) ⊂ off A := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro i hi
        have hm' := mono i A (A ∪ X) Finset.subset_union_left
        have hv : f i (A ∪ X) = false := (Finset.mem_filter.mp hi).2
        rw [hv] at hm'
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm hm' (by simp)⟩
      · intro he
        have hmem : j ∈ off A := by simp [off, flip.1]
        rw [← he] at hmem
        simp [off, flip.2] at hmem
    apply ih (by omega) (A ∪ X)
    · have hdiff : t-r = (t-(r+1))+1 := by omega
      rw [hdiff, Nat.add_mul, Nat.one_mul]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add hA hX)
    · have := Finset.card_lt_card hsub
      omega

open CircuitLowerBounds

theorem countSurviving
    (count : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit)
      (o c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (S i).card) →
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n),
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔
          p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) →
      ∑ i : Fin m, c i ≤ C.size)
    (normalize : ∀ (n : ℕ) (gates : List Gate) (T Z : Finset (Fin n)),
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∃ (gates' : List Gate) (r : ℕ → ℕ),
        (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        gates'.length ≤ gates.length ∧ ∀ o : ℕ,
        (∃ x y : Fin n → Bool,
          Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠
          Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) →
        ∀ x : Fin n → Bool, Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
          Circuit.eval ⟨gates, o⟩
            (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)))
    {n m q k : ℕ} (Fam : Fin m → Finset (Fin n))
    (hcard : ∀ i, (Fam i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (Fam i ∩ Fam j).card ≤ 1)
    (B : Finset (Fin n)) (M : List Gate) (o : Fin m → ℕ)
    (hg : ∀ g ∈ M, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hk : 1 ≤ k)
    (ok : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card ≤ k →
      Circuit.eval ⟨M, o i⟩ (List.ofFn (fun p => if p ∈ B then true else x p)) =
        decide (∃ v ∈ Fam i, (if v ∈ B then true else x v) = true)) :
    min k q * ((Finset.univ : Finset (Fin m)).filter (fun i => Disjoint (Fam i) B)).card ≤
      M.length := by
  classical
  by_cases hq : q = 0
  · simp [hq]
  let D := (Finset.univ : Finset (Fin m)).filter (fun i => Disjoint (Fam i) B)
  let e := D.equivFin.symm
  let line (a : Fin D.card) : Fin m := (e a).val
  have dis (a : Fin D.card) : Disjoint (Fam (line a)) B :=
    (Finset.mem_filter.mp (e a).property).2
  have masked (a : Fin D.card) (x : Fin n → Bool)
      (hx : (Finset.univ.filter (fun p => x p = true)).card ≤ k) :
      Circuit.eval ⟨M, o (line a)⟩ (List.ofFn (fun p => if p ∈ B then true else x p)) =
        decide (∃ v ∈ Fam (line a), x v = true) := by
    rw [ok _ _ hx]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor <;> rintro ⟨v, hv, hv'⟩ <;> refine ⟨v, hv, ?_⟩ <;>
      simpa [Finset.disjoint_left.mp (dis a) hv] using hv'
  have single (p : Fin n) :
      (Finset.univ.filter (fun t : Fin n => decide (t = p) = true)).card ≤ k := by
    have h : Finset.univ.filter (fun t : Fin n => decide (t = p) = true) = {p} := by
      ext; simp
    rw [h, Finset.card_singleton]
    exact hk
  obtain ⟨N, r, hN, hlen, hr⟩ := normalize n M B ∅ hg
  simp only [Finset.notMem_empty, ite_false] at hr
  have transfer (a : Fin D.card) := hr (o (line a))
  have valid (a : Fin D.card) (x : Fin n → Bool)
      (hx : (Finset.univ.filter (fun p => x p = true)).card ≤ k) :
      Circuit.eval ⟨N, r (o (line a))⟩ (List.ofFn x) =
        decide (∃ v ∈ Fam (line a), x v = true) := by
    apply Eq.trans (transfer a ?_ x) (masked a x hx)
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Fam (line a)).card by rw [hcard]; omega)
    refine ⟨fun _ => false, fun t => decide (t = p), ?_⟩
    rw [masked a _ (by simp), masked a _ (single p)]
    simp [hp]
  have bound := count n D.card k (fun a => Fam (line a)) ⟨N, 0⟩
    (fun a => r (o (line a))) (fun _ => min k q)
    (fun i j hij => hinter _ _ (fun h => hij (e.injective (Subtype.ext h))))
    (fun i => by rw [hcard]; omega) hN
    (fun i p => by
      change Circuit.eval ⟨N, r (o (line i))⟩ _ = true ↔ _
      rw [valid i _ (single p)]
      simp)
    (fun i x hx hz => by
      change Circuit.eval ⟨N, r (o (line i))⟩ _ = false
      rw [valid i x hx]
      simp_all)
    (fun _ => min_le_left ..) (fun i => by rw [hcard]; omega)
  change min k q * D.card ≤ M.length
  exact le_trans (by simpa [Circuit.size, Nat.mul_comm] using bound) hlen

end PEqualNP.Outside.L_meta_885

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_885

theorem PEqualNP.Outside.L_meta_885 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length := by
  classical
  intro count normalize n m q F sz inter join deg t k L o ht hk ops cap mono computes K budget finalBound
  let N := {j : Fin L.length | (L.get j).op = GateOp.not}
  let f (j : N) (B : Finset (Fin n)) := wireRead L j.val B
  have fc : Fintype.card N ≤ t := by
    simpa only [Set.ncard_eq_toFinset_card',Set.toFinset_card] using cap
  have fm (j : N) (A B : Finset (Fin n)) (sub : A ⊆ B) : f j A ≤ f j B := by
    apply mono j.val.val (L.get j.val) (by simp) j.property
    intro p
    change decide (p ∈ A) ≤ decide (p ∈ B)
    by_cases h : p ∈ A
    · simp [h,sub h]
    · simp [h]
  obtain ⟨B,stable⟩ := window (k := k) f fm fc
  let live := (Finset.univ.filter (fun i => Disjoint (F i) B)).card
  let loss := (touched F B).card
  have part : live + loss = m := remaining F B
  have touch : loss ≤ B.card*q+1 := touch_bound F join deg B
  have pay (a : ℕ) (apos : 1 ≤ a)
      (agree : ∀ j : N, ∀ X : Finset (Fin n), X.card ≤ a → f j (B ∪ X) = f j B) :
      min a q * live ≤ L.length := by
    let M := frozen L (List.ofFn (bits B))
    have ok := on_window B L F o a (fun j hj X h => agree ⟨j,hj⟩ X h) computes
    have result := countSurviving count normalize F sz inter B M o (frozen_mono L _ ops) apos ok
    simpa only [M,frozen_length] using result
  by_cases q0 : q = 0
  · subst q; simp at finalBound; omega
  have hq : 1 ≤ q := by omega
  rcases stable with ⟨size,all⟩|⟨size,small⟩
  · have p := pay q hq (fun j X _ => all j X)
    rw [min_self] at p
    have b := Nat.mul_le_mul_right q size
    have lossLe : loss ≤ t*k*q+1 := by omega
    have lb := Nat.mul_le_mul_left q lossLe
    rw [← part,Nat.mul_add q live loss] at finalBound
    omega
  · apply le_trans _ (pay k hk small)
    rcases budget with ⟨one,bk,bq⟩|⟨bk,bq⟩
    · have empty : B = ∅ := Finset.card_eq_zero.mp (by simpa [one] using size)
      have lm : live = m := by simp [live,empty]
      rw [lm]
      rcases le_total k q with h|h
      · simpa [min_eq_left h] using bk
      · simpa [min_eq_right h] using bq
    · have b := Nat.mul_le_mul_right q size
      have lossLe : loss ≤ (t-1)*k*q+1 := by omega
      rcases le_total k q with h|h
      · rw [min_eq_left h]
        exact recover_budget K k t k q m live loss ht part lossLe (by simpa [Nat.mul_assoc] using bk)
      · rw [min_eq_right h]
        exact recover_budget K q t k q m live loss ht part lossLe (by simpa [Nat.mul_assoc] using bq)
