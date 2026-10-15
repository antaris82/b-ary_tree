# TASK 05 — Q14 repair report

**Result: counterexample proved** (kernel-checked; the new declarations depend on no axioms).
The former Q14 ("every root- and incidence-preserving automorphism of the full rooted tree is
induced by a levelwise permutation") is false for every alphabet with two distinct letters.

## 1. New declarations (`TreeFoundation/AutomorphismCounterexample.lean`)

Namespace `RayAutomorphism`, ambient `{α : Type} [DecidableEq α]`:

```lean
def condSwap (a b y x : α) : α            -- swap a b x if y = a, else x (decEq branch)
def subtreeSwap (a b : α) : Word α → Word α
  | [] => []
  | [y] => [y]
  | [x, y] => [condSwap a b y x, y]
  | c :: d :: e :: w => c :: subtreeSwap a b (d :: e :: w)

theorem subtreeSwap_subtreeSwap (a b : α) (w : Word α) : subtreeSwap a b (subtreeSwap a b w) = w
theorem subtreeSwap_cons (a b c : α) (p : Word α) :
    ∃ c' : α, subtreeSwap a b (c :: p) = c' :: subtreeSwap a b p
theorem subtreeSwap_isParent (a b : α) {p v : Word α} (h : IsParent p v) :
    IsParent (subtreeSwap a b p) (subtreeSwap a b v)
def subtreeSwapAut (a b : α) : TreeAut α          -- toFun = invFun = subtreeSwap a b
theorem subtreeSwapAut_root (a b : α) : (subtreeSwapAut a b).toFun root = root
theorem subtreeSwap_level_one (a b y : α) : subtreeSwap a b [y] = [y]
theorem subtreeSwap_aa (a b : α) : subtreeSwap a b [a, a] = [b, a]
theorem subtreeSwap_ba (a b : α) (hab : a ≠ b) : subtreeSwap a b [b, a] = [a, a]
theorem subtreeSwap_ab (a b : α) (hab : a ≠ b) : subtreeSwap a b [a, b] = [a, b]
theorem subtreeSwap_append (a b x y : α) (w : Word α) :
    subtreeSwap a b (w ++ [x, y]) = w ++ [condSwap a b y x, y]
theorem subtreeSwap_append_aa (a b : α) (w : Word α) : subtreeSwap a b (w ++ [a, a]) = w ++ [b, a]
theorem subtreeSwap_append_ba (a b : α) (hab : a ≠ b) (w : Word α) :
    subtreeSwap a b (w ++ [b, a]) = w ++ [a, a]
theorem subtreeSwap_append_fixed (a b x y : α) (h : y ≠ a ∨ (x ≠ a ∧ x ≠ b)) (w : Word α) :
    subtreeSwap a b (w ++ [x, y]) = w ++ [x, y]

theorem subtreeSwapAut_not_levelwise (a b : α) (hab : a ≠ b) (P : LevelPerm α) :
    (treeAut P).toFun ≠ (subtreeSwapAut a b).toFun
theorem levelwise_converse_false (a b : α) (hab : a ≠ b) :
    ¬ ∀ T : TreeAut α, ∃ P : LevelPerm α, (treeAut P).toFun = T.toFun
```

Root namespace:

```lean
theorem binary_levelwise_converse_false :
    ¬ ∀ T : RayAutomorphism.TreeAut (Child two),
      ∃ P : RayAutomorphism.LevelPerm (Child two), (RayAutomorphism.treeAut P).toFun = T.toFun
theorem omega_levelwise_converse_false :
    ¬ ∀ T : RayAutomorphism.TreeAut TreeN,
      ∃ P : RayAutomorphism.LevelPerm TreeN, (RayAutomorphism.treeAut P).toFun = T.toFun
```

The binary instance uses the existing letters `Child.first`, `Child.second` and
`Child.first_ne_second`. The omega instance uses `zero ≠ one` in `TreeN`. No new infrastructure
was needed.

## 2. The counterexample

Words list the deepest letter first, so `c :: p` is the child of `p` along letter `c`. Fix letters
`a ≠ b`. The map `subtreeSwap a b` swaps the child subtrees rooted at `a :: [a]` and `b :: [a]`.
Every descendant `w ++ [a, a]` goes to `w ++ [b, a]` and back (`subtreeSwap_append_aa/_ba`). All
first-level vertices are fixed, and so is every other subtree (`subtreeSwap_append_fixed`).

* It is its own explicit inverse, preserves the root, and preserves parent incidence
  (`subtreeSwap_cons`). Since it is an involution it also reflects incidence. Together these give
  the `TreeAut` structure.
* **Levelwise vs vertex-dependent.** A `LevelPerm` uses the same permutation `P.perm n` for the
  new letter of every vertex at depth `n + 1`, whatever its parent. `subtreeSwap` permutes the
  children of `[a]` by the swap `(a b)` and the children of every other first-level vertex by
  the identity. Both kinds of first-level vertex sit at the same depth `one`.
* **The not-levelwise proof.** `wordAct P [a, a] = P.perm (depth [a]) a :: [P.perm zero a]` and
  `wordAct P [a, b] = P.perm (depth [b]) a :: [P.perm zero b]`.
  * The level-zero permutation `P.perm zero` moves only the parent letters, and plays no part in
    the comparison of the new letters.
  * `depth [a] = depth [b]` holds by `rfl`, so both new letters equal `P.perm one a`.
  * `subtreeSwap` gives the new letters `b` (`subtreeSwap_aa`) and `a` (`subtreeSwap_ab`).
  * Equal `toFun` maps would therefore force `b = P.perm one a = a`, which contradicts `a ≠ b`.

The old theorems `RayAutomorphism.treeAut`, `invariant_const` and `swapInvariant_const` are
unchanged and still valid. The counterexample does not invalidate them.

## 3. Changed files

* new: `TreeFoundation/AutomorphismCounterexample.lean`, `TASK05_Q14_REPAIR_REPORT.md`
* `TreeFoundations.lean`: one import line.
* `ReleaseAudit/Run.lean`: `#require_decls` gains `RayAutomorphism.subtreeSwapAut`,
  `RayAutomorphism.subtreeSwapAut_not_levelwise`, `RayAutomorphism.levelwise_converse_false` and
  `binary_levelwise_converse_false`, for 47 in total.
* `scripts/gen_matrix.py`: one appended row. The regenerated `FINAL_AXIOM_AND_LAW_MATRIX.md` now
  has row 156, status `PROVED`, axioms `[]`. Counts: PROVED 129, CONDITIONAL 9, OBSTRUCTION 6,
  OPEN 11, DEFINITION_ONLY 1. `release/declaration_signatures.txt` was regenerated too
  (441 declarations).
* `FINAL_OPEN_QUESTIONS.md`: Q14 replaced by the corrected statement and its status.
* `VERIFICATION_LOG.md`: §2 correction and the new §4a (the final run). The Q14-related counts were
  updated.
* `release/verification_output.txt`, `release/source_inventory.txt` and `release/module_dag.txt`
  were regenerated from the final files.
* `scripts/*.sh` and `scripts/*.py`: the executable bit was restored (the content is unchanged).

These files were not changed: `FINAL_OPEN_PROBLEMS.md` and `FINAL_FOUNDATIONS_REPORT.md` do not
state the false converse; `VERIFICATION_LOG.md` §5 lists them as historical records. No carrier,
relation, operation or existing theorem was changed. All qualifications on `TreeR` are
unchanged: completeness, apartness, Markov, LPO, WLPO and choice.

## 4. Verification

* Targeted build: `lake build TreeFoundation.AutomorphismCounterexample` succeeded with
  `Build completed successfully (18 jobs)`.
* Axioms: `#print axioms` reports "does not depend on any axioms" for each of `subtreeSwapAut`,
  `subtreeSwapAut_not_levelwise`, `levelwise_converse_false`, `subtreeSwap_append_fixed`,
  `binary_levelwise_converse_false` and `omega_levelwise_converse_false`.
* Release run (once, on the frozen tree at commit `87b834886218224101a36ffdb7367ab4370f00b2`):
  `./scripts/verify_release.sh` took 4 min 13 s and exited with **exit 0**.
  * Before it, a first invocation failed with `Permission denied` before running any step, because
    the script had lost its executable bit. No step executed then.
  * 73 source files.
  * **Fingerprint `44a6935b4ecb8de9a4215976eddd31da05f18f5a6b400c56ae7efbb7f2b52075`**.
  * Build: `Build completed successfully (65 jobs)`.
  * Source check passed, with 62 files scanned and reachable.
  * Fail-closed audit passed: 62 modules and 2975 constants. 2148 are axiom-free, 245 use
    `propext`, 792 use `Quot.sound`, and no axiom lies outside `[propext, Quot.sound]`. All 47
    required declarations are present.
  * Negative fixtures: all expectations met.
  * `leanchecker`: `--fresh` on both roots and replay of all seven prefixes, `ok (exit 0)` each.
  * Final line: `RELEASE VERIFICATION PASSED`.
  * The full output is in `release/verification_output.txt`.

## 5. Remaining open obligations

* None for the repaired Q14.
* By design, the full automorphism group was not classified. For example, "every automorphism is
  given by a vertex-dependent family of child permutations" is neither claimed nor formalized.
* `scripts/inventory.py` cannot run in this checkout: its baseline commit `4cc0749` is not in the
  git history. The inventory was regenerated with the same logic, keeping the recorded provenance
  labels.
* The informational axiom report `ReleaseAudit/Report.lean` does not list the new declarations.
  The enforcing audit covers them.
