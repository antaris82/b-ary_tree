module

public import BoundaryTopology.ManifoldConditions

@[expose] public section

/-!
# Checkpoint G4 — positive control: the completed line `TreeR K` as a one-chart `1`-manifold

This file is about the completion `TreeR K` itself (with its interval topology
`realTopology K`), **not** about any tree boundary.

* `ofQ_eps_lt_of_pos`: every positive real exceeds some `ofQ (eps k)`;
* `lt_open_left`, `lt_open_right`: open rays `{w | w < y}`, `{w | y < w}` are open;
* `separate_of_lt`: two reals with a **positive separation witness** `x < y` lie in disjoint open
  sets (Hausdorff separation in the constructive, witness-based form; mere `x ≠ y` is not used);
* `realIdChart`: the identity is a global chart of `TreeR K` onto the model line `TreeR K`, so
  `TreeR K` is a one-chart topological `1`-manifold in the sense of the chart structure `Chart`
  (with model space the line itself).  This is a statement about the line only.
-/

open TreeN ListOps Word CSR CRing TOField TreeR Topology

namespace TreeR

variable {K : Type} [TOField K]

/-- Every positive real dominates some precision `ofQ (eps k)`. -/
theorem ofQ_eps_lt_of_pos {d : TreeR K} (h : 𝟘 < d) : ∃ k : TreeN, ofQ (eps k) < d := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_between h
  have hq : (𝟘 : K) < q := lt_of_ofQ_lt hq1
  obtain ⟨k, hk⟩ := exists_eps_lt hq
  exact ⟨k, TreeR.lt_trans (ofQ_lt_ofQ hk) hq2⟩

theorem rpos_sub_of_lt {x y : TreeR K} (h : x < y) : RPos (y + -x) := h

theorem pos_sub_of_lt {x y : TreeR K} (h : x < y) : (𝟘 : TreeR K) < y + -x :=
  (pos_iff (y + -x)).2 h

/-- Open left rays are open in the interval topology. -/
theorem lt_open_left (y : TreeR K) : (realTopology K).IsOpen (fun w => w < y) := by
  intro z hz
  obtain ⟨k, hk⟩ := ofQ_eps_lt_of_pos (pos_sub_of_lt hz)
  refine ⟨k, fun w hw => ?_⟩
  have h1 : RPos (y + -z + -ofQ (eps k)) := hk
  have h2 : RPos (z + ofQ (eps k) + -w) := hw.2
  have e : y + -z + -ofQ (eps k) = y + -(z + ofQ (eps k)) := by
    rw [neg_add, CSR.add_assoc]
  rw [e] at h1
  show RPos (y + -w)
  rw [← sub_add_sub y (z + ofQ (eps k)) w]
  exact rpos_add h1 h2

/-- Open right rays are open in the interval topology. -/
theorem lt_open_right (y : TreeR K) : (realTopology K).IsOpen (fun w => y < w) := by
  intro z hz
  obtain ⟨k, hk⟩ := ofQ_eps_lt_of_pos (pos_sub_of_lt hz)
  refine ⟨k, fun w hw => ?_⟩
  have h1 : RPos (z + -y + -ofQ (eps k)) := hk
  have h2 : RPos (w + -(z + -ofQ (eps k))) := hw.1
  have e : z + -y + -ofQ (eps k) = z + -ofQ (eps k) + -y := by
    rw [CSR.add_assoc, CSR.add_comm (-y), ← CSR.add_assoc]
  rw [e] at h1
  show RPos (w + -y)
  rw [← sub_add_sub w (z + -ofQ (eps k)) y]
  exact rpos_add h2 h1

/-- **Separation under a positive witness**: if `x < y` there are disjoint open sets containing
`x` and `y` respectively. -/
theorem separate_of_lt {x y : TreeR K} (h : x < y) :
    ∃ U V : TreeR K → Prop, (realTopology K).IsOpen U ∧ (realTopology K).IsOpen V ∧
      U x ∧ V y ∧ ∀ w, U w → V w → False := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_between h
  exact ⟨fun w => w < ofQ q, fun w => ofQ q < w, lt_open_left _, lt_open_right _, hq1, hq2,
    fun w h1 h2 => TreeR.lt_irrefl w (TreeR.lt_trans h1 h2)⟩

/-- **The identity global chart** of the line `TreeR K` (model space: the line itself).
**Sanity check, not a substantive theorem:** the chart maps are identities and the domains are
`True`; it only records that the interval topology is a topology in which the identity is a
homeomorphism. -/
def realIdChart (K : Type) [TOField K] : Chart (realTopology K) (realTopology K) where
  U := fun _ => True
  V := fun _ => True
  U_open := (realTopology K).isOpen_univ
  V_open := (realTopology K).isOpen_univ
  f := fun x => x
  g := fun y => y
  maps_f := fun _ _ => True.intro
  maps_g := fun _ _ => True.intro
  gf := fun _ _ => rfl
  fg := fun _ _ => rfl
  f_cont := fun W hW x hx => by
    obtain ⟨k, hk⟩ := hW x hx.2
    exact ⟨k, fun y hy => ⟨True.intro, hk y hy⟩⟩
  g_cont := fun W hW x hx => by
    obtain ⟨k, hk⟩ := hW x hx.2
    exact ⟨k, fun y hy => ⟨True.intro, hk y hy⟩⟩

/-- The identity chart covers every point (tautological: its domain is `True`). -/
theorem realIdChart_covers (x : TreeR K) : (realIdChart K).U x := True.intro

end TreeR

end
