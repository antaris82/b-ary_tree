module

public import BoundaryTopology.TopologicalObstructions
public import TreeAnalysis.Instances

@[expose] public section

/-!
# Checkpoint G — manifold questions: definitions, no-go theorems, conditions

* `Topology.Chart TX TY`: a local homeomorphism between an open set `U` of `X` and an open set
  `V` of `Y` (mutually inverse maps, both continuous on their domains).
* `chart_connected_subsingleton`: for the **natural prefix topology** on rays over any alphabet
  with decidable letter equality, every connected subset of the target of a chart is a
  subsingleton (connectedness is transported by the chart, and the boundary is totally
  disconnected).
* **Dimension `0`** (target: the one-point space): for `b ≥ 2` and omega branching there is no
  chart at any point (`no_zero_dim_chart`: no isolated points); for `b = one` the whole boundary
  is a one-chart `0`-manifold (`unary_zero_manifold`).
* **Dimension `≥ 1`**: `no_chart_of_connectedPairs` excludes charts into every space in which each
  inhabited open set contains a connected subset with two distinct points.  For the real line
  `TreeR K` with its interval topology `realTopology K`, this property follows from the
  connectedness of open intervals (`IntervalsConnected K`), which is **not proved** here; the
  resulting obstruction `no_chart_into_real` is therefore **conditional** on that premise.
  (`TreeR^d` for `d ≥ 2` is not formalized; the generic theorem applies to any target with the
  stated property.)
* The algebraic transverse rank `b − 1` of Task 01 plays no role in any of these statements.
-/

open TreeN ListOps Word CSR CRing TOField TreeR

namespace Topology

variable {X Y : Type} (TX : Topology X) (TY : Topology Y)

/-- Continuity of `f` on an open set `U` (relative preimages of open sets are open). -/
def ContinuousOn (f : X → Y) (U : X → Prop) : Prop :=
  ∀ W, TY.IsOpen W → TX.IsOpen (fun x => U x ∧ W (f x))

/-- A chart: a homeomorphism between an open subset of `X` and an open subset of `Y`. -/
structure Chart where
  U : X → Prop
  V : Y → Prop
  U_open : TX.IsOpen U
  V_open : TY.IsOpen V
  f : X → Y
  g : Y → X
  maps_f : ∀ x, U x → V (f x)
  maps_g : ∀ y, V y → U (g y)
  gf : ∀ x, U x → g (f x) = x
  fg : ∀ y, V y → f (g y) = y
  f_cont : ContinuousOn TX TY f U
  g_cont : ContinuousOn TY TX g V

variable {TX TY}

/-- Charts transport connected subsets of the target back to the source. -/
theorem chart_connected_transport (c : Chart TX TY) {W : Y → Prop} (hWV : ∀ y, W y → c.V y)
    (hW : TY.Connected W) : TX.Connected (fun x => c.U x ∧ W (c.f x)) := by
  intro U1 V1 hU1 hV1 hcov hdis ⟨x1, hx1, hx1U⟩ ⟨x2, hx2, hx2V⟩
  apply hW (fun y => c.V y ∧ U1 (c.g y)) (fun y => c.V y ∧ V1 (c.g y))
    (c.g_cont U1 hU1) (c.g_cont V1 hV1)
  · intro y hy
    have hS : c.U (c.g y) ∧ W (c.f (c.g y)) := ⟨c.maps_g y (hWV y hy), by rw [c.fg y (hWV y hy)]; exact hy⟩
    cases hcov _ hS with
    | inl h => exact Or.inl ⟨hWV y hy, h⟩
    | inr h => exact Or.inr ⟨hWV y hy, h⟩
  · intro y hy h1 h2
    exact hdis _ ⟨c.maps_g y (hWV y hy), by rw [c.fg y (hWV y hy)]; exact hy⟩ h1.2 h2.2
  · exact ⟨c.f x1, hx1.2, c.maps_f x1 hx1.1, by rw [c.gf x1 hx1.1]; exact hx1U⟩
  · exact ⟨c.f x2, hx2.2, c.maps_f x2 hx2.1, by rw [c.gf x2 hx2.1]; exact hx2V⟩

/-- Targets in which every inhabited open set contains a connected subset with two distinct
points (the property used to exclude charts of dimension `≥ 1`). -/
def HasConnectedPairs (TY : Topology Y) : Prop :=
  ∀ V : Y → Prop, TY.IsOpen V → (∃ y, V y) →
    ∃ W : Y → Prop, (∀ y, W y → V y) ∧ TY.Connected W ∧ ∃ y1 y2, W y1 ∧ W y2 ∧ y1 ≠ y2

/-- The one-point space. -/
def pointTopology : Topology Unit where
  IsOpen := fun _ => True
  isOpen_univ := True.intro
  isOpen_inter := fun _ _ _ _ => True.intro
  isOpen_union := fun _ _ _ => True.intro

end Topology

open Topology

namespace Ray

variable {α : Type} {Y : Type} {TY : Topology Y}

/-- In a chart of the natural prefix topology, connected subsets of the target are
subsingletons. -/
theorem chart_connected_subsingleton [DecidableEq α] (c : Chart (prefixTopology α) TY)
    {W : Y → Prop} (hWV : ∀ y, W y → c.V y) (hW : TY.Connected W) {y1 y2 : Y}
    (h1 : W y1) (h2 : W y2) : y1 = y2 := by
  have hS := chart_connected_transport c hWV hW
  have m1 : c.U (c.g y1) ∧ W (c.f (c.g y1)) :=
    ⟨c.maps_g y1 (hWV y1 h1), by rw [c.fg y1 (hWV y1 h1)]; exact h1⟩
  have m2 : c.U (c.g y2) ∧ W (c.f (c.g y2)) :=
    ⟨c.maps_g y2 (hWV y2 h2), by rw [c.fg y2 (hWV y2 h2)]; exact h2⟩
  have e := connected_subsingleton hS m1 m2
  rw [← c.fg y1 (hWV y1 h1), ← c.fg y2 (hWV y2 h2), e]

/-- **No-go (dimension `≥ 1`, generic target)**: no chart of the natural prefix topology at any
point into a space with connected pairs in every inhabited open set. -/
theorem no_chart_of_connectedPairs [DecidableEq α] (hY : HasConnectedPairs TY)
    (c : Chart (prefixTopology α) TY) (hx : ∃ x, c.U x) : False := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨W, hWV, hW, y1, y2, h1, h2, hne⟩ := hY c.V c.V_open ⟨c.f x, c.maps_f x hx⟩
  exact hne (chart_connected_subsingleton c hWV hW h1 h2)

/-- **No-go (dimension `0`)**: for `b ≥ 2` and omega branching, no chart into the one-point
space exists at any point. -/
theorem no_zero_dim_chart [DecidableEq α] [TwoLetters α] (c : Chart (prefixTopology α) pointTopology)
    (hx : ∃ x, c.U x) : False := by
  obtain ⟨r, hr⟩ := hx
  obtain ⟨r', n, hr', hne⟩ := no_isolated c.U_open hr
  have e : r' = r := by
    rw [← c.gf r' hr', ← c.gf r hr]
  rw [e] at hne
  exact hne rfl

/-- **Unary branching**: the boundary is a one-chart `0`-manifold (homeomorphic to a point). -/
def unaryChart : Chart (prefixTopology (Child TreeN.one)) pointTopology where
  U := fun _ => True
  V := fun _ => True
  U_open := (prefixTopology _).isOpen_univ
  V_open := True.intro
  f := fun _ => ()
  g := fun _ => const (Child.first (zero_lt_succ TreeN.zero))
  maps_f := fun _ _ => True.intro
  maps_g := fun _ _ => True.intro
  gf := fun x _ => unary_ray_unique _ x
  fg := fun y _ => by cases y; rfl
  f_cont := fun _ _ _ h => ⟨TreeN.zero, fun _ _ => h⟩
  g_cont := fun _ _ => True.intro

/-- **Immediate lemma / sanity check:** coverage holds tautologically because the chart domain of
`unaryChart` is the constant predicate `True`; the content of the unary `0`-manifold statement
lies in the chart itself (`unary_ray_unique`). -/
theorem unary_zero_manifold : ∀ x, unaryChart.U x := fun _ => True.intro

end Ray

/-! ## The interval topology of `TreeR` and the conditional obstruction in dimension `1` -/

namespace TreeR

variable {K : Type} [TOField K]

/-- The open ball of radius `eps k` around `x`. -/
def Ball (x : TreeR K) (k : TreeN) (y : TreeR K) : Prop :=
  x + -ofQ (eps k) < y ∧ y < x + ofQ (eps k)

theorem neg_le_neg {a b : TreeR K} (h : a ≤ b) : -b ≤ -a := by
  show RNonneg (-a + - -b)
  rw [neg_neg, CSR.add_comm]
  exact h

theorem ball_mono {x y : TreeR K} {k k' : TreeN} (h : PathLE k k') (hy : Ball x k' y) :
    Ball x k y := by
  have he : ofQ (eps (K := K) k') ≤ ofQ (eps k) := ofQ_le_ofQ (eps_le_eps h)
  exact ⟨lt_of_le_of_lt (add_le_add_left x (neg_le_neg he)) hy.1,
    lt_of_lt_of_le hy.2 (add_le_add_left x he)⟩

/-- The interval topology on `TreeR K`. -/
def realTopology (K : Type) [TOField K] : Topology (TreeR K) where
  IsOpen := fun U => ∀ x, U x → ∃ k : TreeN, ∀ y, Ball x k y → U y
  isOpen_univ := fun _ _ => ⟨TreeN.zero, fun _ _ => True.intro⟩
  isOpen_inter := fun U V hU hV x h => by
    obtain ⟨k1, h1⟩ := hU x h.1
    obtain ⟨k2, h2⟩ := hV x h.2
    exact ⟨maxN k1 k2, fun y hy => ⟨h1 y (ball_mono (le_maxN_left _ _) hy),
      h2 y (ball_mono (le_maxN_right _ _) hy)⟩⟩
  isOpen_union := fun _ F hF x h => by
    obtain ⟨i, hi⟩ := h
    obtain ⟨k, hk⟩ := hF i x hi
    exact ⟨k, fun y hy => ⟨i, hk y hy⟩⟩

theorem ofQ_eps_pos (k : TreeN) : RPos (ofQ (eps (K := K) k)) := rpos_mk (seqPos_const (eps_pos k))

theorem lt_add_eps (x : TreeR K) (k : TreeN) : x < x + ofQ (eps k) := by
  show RPos (x + ofQ (eps k) + -x)
  rw [CSR.add_comm x, add_sub_cancel_right]
  exact ofQ_eps_pos k

theorem sub_eps_lt (x : TreeR K) (k : TreeN) : x + -ofQ (eps k) < x := by
  show RPos (x + -(x + -ofQ (eps k)))
  rw [neg_add, neg_neg, ← CSR.add_assoc, add_neg_cancel, CSR.zero_add]
  exact ofQ_eps_pos k

theorem mem_ball_self (x : TreeR K) (k : TreeN) : Ball x k x := ⟨sub_eps_lt x k, lt_add_eps x k⟩

theorem mem_ball_shift (x : TreeR K) (k : TreeN) : Ball x k (x + ofQ (eps (succ k))) := by
  refine ⟨lt_trans (sub_eps_lt x k) (lt_add_eps x (succ k)), ?_⟩
  show RPos (x + ofQ (eps k) + -(x + ofQ (eps (succ k))))
  rw [add_sub_add_left, ← ofQ_neg, ← ofQ_add]
  apply rpos_mk
  apply seqPos_const
  have h := TOField.add_lt_add_right (-eps (K := K) (succ k)) (eps_succ_lt k)
  rw [add_neg_cancel] at h
  exact h

/-- The connectedness of the open intervals of `TreeR K` (not proved here). -/
def IntervalsConnected (K : Type) [TOField K] : Prop :=
  ∀ (x : TreeR K) (k : TreeN), (realTopology K).Connected (Ball x k)

/-- Connected intervals give connected pairs in every inhabited open set. -/
theorem connectedPairs_of_intervals (h : IntervalsConnected K) :
    HasConnectedPairs (realTopology K) := by
  intro V hV ⟨y, hy⟩
  obtain ⟨k, hk⟩ := hV y hy
  refine ⟨Ball y k, hk, h y k, y, y + ofQ (eps (succ k)), mem_ball_self y k, mem_ball_shift y k,
    fun e => lt_irrefl y ?_⟩
  have h2 := lt_add_eps y (succ k)
  rw [← e] at h2
  exact h2

end TreeR

/-- **Conditional no-go in dimension `1`**: if the open intervals of `TreeR K` are connected,
no point of the boundary (natural prefix topology, decidable letters) has a chart into the
real line `TreeR K`. -/
theorem no_chart_into_real {α K : Type} [DecidableEq α] [TOField K]
    (hI : TreeR.IntervalsConnected K) (c : Chart (Ray.prefixTopology α) (TreeR.realTopology K))
    (hx : ∃ x, c.U x) : False :=
  Ray.no_chart_of_connectedPairs (TreeR.connectedPairs_of_intervals hI) c hx

end
