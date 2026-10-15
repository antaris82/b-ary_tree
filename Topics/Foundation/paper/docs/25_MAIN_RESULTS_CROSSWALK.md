# Abgleich der 25 ausdrücklich gesetzten Hauptresultate (Task 06)

**Status:** Quellenbasierte Review-Matrix, keine erneute Elaborierung. Die genauen Typen sind vor Freigabe aus `proof_correspondence.md` gegen die Lean-Signaturen zu lesen; kurze Referenzangaben hier sind Navigationspunkte.

## 1. Unique finite root path (proposition, main.tex:181)

**Wortlaut der mathematischen Satzbehauptung:** For every word $w$, there is exactly one oriented finite edge list from $\epsilon$ to $w$ in the prescribed parent--child incidence relation.

**Lean-Anker:** `Word.dpath_root_unique`. **Beweiskette:** Unique parent; induction on terminal word. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 2. Path sum equals depth (proposition, main.tex:218)

**Wortlaut der mathematischen Satzbehauptung:** For every finite word $w$, $s(w)=d(w)$.

**Lean-Anker:** `Word.pathSum_eq_depth`. **Beweiskette:** Induction over actual finite root-edge list. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 3. Natural semiring (proposition, main.tex:252)

**Wortlaut der mathematischen Satzbehauptung:** The carrier $\N$ with these operations is a commutative semiring with distinct zero and one and the induction/recursion properties of unary words.

**Lean-Anker:** `TreeN.instCSR; TreeN.recN_unique`. **Beweiskette:** Unary recursion, distributivity and cancellation. **Review-Änderung:** proof detail. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 4. Transitivity and positive-denominator cancellation (lemma, main.tex:361)

**Wortlaut der mathematischen Satzbehauptung:** The relation \eqref{eq:fracrel} is an equivalence relation.

**Lean-Anker:** `Frac.eqv_trans`. **Beweiskette:** Cross-product cancellation with strictly positive denominator. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 5. Fraction-field algebra (proposition, main.tex:392)

**Wortlaut der mathematischen Satzbehauptung:** The quotient $\Frac(\Z)=\mathcal F/\!\sim_F$ with \eqref{eq:fracops} and the zero-inverse convention is a field of characteristic zero.

**Lean-Anker:** `FracQ.instTField`. **Beweiskette:** Positive-denominator sign cases and quotient operation compatibility. **Review-Änderung:** proof detail. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 6. Ordered-field comparison (theorem, main.tex:468)

**Wortlaut der mathematischen Satzbehauptung:** For every alphabet $A$ equipped with two distinct letters, the maps \[ \Phi_A:\Q(A)\longrightarrow\Frac(\Z),\qquad [t]\longmapsto[(a(t),d(t))], \] \[ \Psi_A:\Frac(\Z)\longrightarrow\Q(A) \] where $\Psi_A$ uses the explicit triple witnesses, are mutually inverse ordered-field isomorphisms.

**Lean-Anker:** `TreeQ.orderedFieldIsoFracQ`. **Beweiskette:** Explicitly state transported operations via the fraction quotient. **Review-Änderung:** M02 transport. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 7. Arity independence (corollary, main.tex:488)

**Wortlaut der mathematischen Satzbehauptung:** If $A$ and $B$ are alphabets each equipped with two distinct letters, then $\Q(A)\cong\Q(B)$ as ordered fields. In particular finite arities $b,c\ge2$ have isomorphic rational fields.

**Lean-Anker:** `TreeQ.arityIso; TreeQ.transfer_le`. **Beweiskette:** Add order preservation and reflection through inverse. **Review-Änderung:** M08 order. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 8. Symmetric bilinearity of the finite coordinate form (proposition, main.tex:527)

**Wortlaut der mathematischen Satzbehauptung:** For every finite $b$ (including $b=0$) and every coefficient carrier $K$ satisfying the specified field interface, the function $B_b:F_b\times F_b\to K$ is symmetric and bilinear. Explicitly, for all $x,y,z\in F_b$ and $a\in K$, \begin{align*} B_b(x+y,z)&=B_b(x,z)+B_b(y,z),& B_b(x,y+z)&=B_b(x,y)+B_b(x,z),\\ B_b(ax,y)&=aB_b(x,y),& B_b(x,ay)&=aB_b(x,y),\\ B_b(x,y)&=B_b(y,x). \end{align*} The zero and additive-inverse identities follow as well.

**Lean-Anker:** `ChildModule.dot_bilinear_symmetric; ChildModule.dot_addV_left`. **Beweiskette:** Direct finite-sum bilinearity. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 9. Explicit bases and ranks (theorem, main.tex:570)

**Wortlaut der mathematischen Satzbehauptung:** For each positive finite arity $b$, $\{u_b\}$ is a basis of $L_b$, and \[ \mathcal B_b=\{e_j-e_0:1\le j<b\} \] is a basis of $S_b$. In particular, \[ \dim_KL_b=1,\qquad\dim_KS_b=b-1. \]

**Lean-Anker:** `ChildModule.longitudinal_basis; ChildModule.transverse_basis`. **Beweiskette:** Positive arity, basis cardinality b−1, TField. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 10. Finite decomposition (theorem, main.tex:607)

**Wortlaut der mathematischen Satzbehauptung:** For $b>0$ in a field of characteristic zero, define \[ P_L(x)=b^{-1}\sigma_b(x)u_b,\qquad P_S(x)=x-P_L(x). \] The identity $x=P_L(x)+P_S(x)$ holds for every $b$, while the positive-arity hypothesis gives $P_L(x)\in L_b$, $P_S(x)\in S_b$ and the uniqueness of the longitudinal--transverse decomposition. Hence $F_b=L_b\oplus S_b$.

**Lean-Anker:** `ChildModule.decomposition; ChildModule.decomposition_unique`. **Beweiskette:** Distinguish algebraic identity from nonzero arity requirement. **Review-Änderung:** M09 hypotheses. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 11. Complementary projection operators (theorem, main.tex:623)

**Wortlaut der mathematischen Satzbehauptung:** Let $b>0$ and let $K$ satisfy the characteristic-zero field interface above. The maps $P_L,P_S:F_b\to F_b$ are linear, and for every $x\in F_b$, \begin{gather*} P_L^2 x=P_Lx,\qquad P_S^2x=P_Sx,\qquad P_LP_Sx=P_SP_Lx=0,\\ P_Lx+P_Sx=x. \end{gather*} Their images and kernels are exactly \[ \operatorname{im}P_L=L_b=\ker P_S,\qquad \operatorname{im}P_S=S_b=\ker P_L. \] In particular, the longitudinal and transverse components are fixed by their respective projections and annihilated by the complementary projection.

**Lean-Anker:** `ChildModule.projL_idem; ChildModule.projS_idem; ChildModule.range_projL; ChildModule.range_projS`. **Beweiskette:** Task 06 projection laws. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 12. Algebraic orthogonal splitting (theorem, main.tex:665)

**Wortlaut der mathematischen Satzbehauptung:** Under the hypotheses of Theorem~\ref{thm:projectionlaws}, \[ B_b(\ell,s)=B_b(s,\ell)=0\qquad (\ell\in L_b,\ s\in S_b). \] For all $x,y\in F_b$, one consequently has \begin{equation}\label{eq:bilinearsplit} B_b(x,y)=B_b(P_Lx,P_Ly)+B_b(P_Sx,P_Sy). \end{equation}

**Lean-Anker:** `ChildModule.dot_split; ChildModule.dot_inL_inS`. **Beweiskette:** Cross terms vanish from orthogonality. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 13. Countable transverse basis (theorem, main.tex:714)

**Wortlaut der mathematischen Satzbehauptung:** The finitely supported vectors $v_i=e_{i+1}-e_0$, $i\in\N$, are linearly independent and algebraically span $S_\omega$.

**Lean-Anker:** `OmegaModule.tvO_indep; OmegaModule.tvO_span`. **Beweiskette:** Finitely supported algebraic span, no convergence. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 14. Longitudinal incompatibility for zero-padding (theorem, main.tex:736)

**Wortlaut der mathematischen Satzbehauptung:** For positive finite arity $b$, the zero-padding image of the uniform vector $u_b$ does not belong to the uniform line $L_{b+1}$. Moreover the everywhere-one function on $\N$ is not an element of $K^{(\N)}$.

**Lean-Anker:** `Longitudinal.padSucc_u_not_inL; Longitudinal.allOnes_not_finSupp`. **Beweiskette:** Zero-padding obstruction only. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 15. Separated rays (proposition, main.tex:785)

**Wortlaut der mathematischen Satzbehauptung:** If two rays differ at a specified index, disjoint clopen cylinders separate them. If only the negation of their equality is given constructively, the source proves a double-negated disagreement statement; a specific disagreement index cannot be silently inferred without its required logical premise.

**Lean-Anker:** `Ray.separate_of_diff; Ray.cyl_compl_open`. **Beweiskette:** Use actual finite witness of disagreement. **Review-Änderung:** M10 premise. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 16. Noncompact countable cylinders (proposition, main.tex:812)

**Wortlaut der mathematischen Satzbehauptung:** In the source's open-cover definition of compactness, no cylinder in $\N^{\N}$ is compact. Consequently the countably branching boundary is not locally compact at any point in its corresponding neighborhood definition.

**Lean-Anker:** `Ray.cyl_not_compact; Ray.not_locallyCompactAt`. **Beweiskette:** Open-cover argument in project topology. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 17. Ray transitivity and invariant maps (proposition, main.tex:850)

**Wortlaut der mathematischen Satzbehauptung:** For an alphabet with decidable equality, the levelwise family of automorphisms acts transitively on its ray space. Hence every function from that ray space to any codomain which is invariant under all such actions is constant.

**Lean-Anker:** `RayAutomorphism.rayAct_swapPerm; RayAutomorphism.invariant_const`. **Beweiskette:** Levelwise subgroup transitivity. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 18. Product estimate and modulus (lemma, main.tex:947)

**Wortlaut der mathematischen Satzbehauptung:** Suppose the modulated sequences $s,t$ have finite eventual bounds $|s_n|\le 2^{B_s}$ and $|t_n|\le2^{B_t}$ on specified tails, where $B_s,B_t\in\N$. Then, after adding the bounds for those tails, a product modulus is \[ \mu_{st}(k)=\max\bigl\{N_s,N_t, \mu_s(k+1+B_t),\mu_t(k+1+B_s)\bigr\}. \]

**Lean-Anker:** `TOField.mulMod; TOField.mulMod_isMod; TOField.mulSeq_resp`. **Beweiskette:** Product bound/choice of shift; check exact declaration mapping. **Review-Änderung:** proof detail. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 19. Constructive Cauchy ring (proposition, main.tex:972)

**Wortlaut der mathematischen Satzbehauptung:** The quotient $\RR(K)$ is a nontrivial commutative ring, and the constant-sequence embedding $\iota:K\hookrightarrow\RR(K)$ is an injective ring homomorphism.

**Lean-Anker:** `TreeR.instCRing; TreeR.ofQ_injective`. **Beweiskette:** Quotient congruence and ring laws. **Review-Änderung:** proof detail. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 20. Order and tight apartness (proposition, main.tex:1010)

**Wortlaut der mathematischen Satzbehauptung:** These relations satisfy transitivity of strict and non-strict order, antisymmetry of $\le$, the proved addition and positive-multiplication compatibility laws, strict cotransitivity, and tightness \[ \neg(x\Apt y)\Longrightarrow x=y. \] They do not supply an unconditional trichotomy for arbitrary $x,y$.

**Lean-Anker:** `TreeR.lt_cotrans; TreeR.eq_of_not_apart`. **Beweiskette:** Exact positivity/nonnegativity quantifiers. **Review-Änderung:** M07 quantifiers. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 21. Separated inversion (theorem, main.tex:1057)

**Wortlaut der mathematischen Satzbehauptung:** For $x\in\RR(K)$, if $x\Apt0$ then there exists $y\in\RR(K)$ with $xy=1$. No unconditional inference of this form from $x\ne0$ is made.

**Lean-Anker:** `TreeR.exists_inv_of_apart`. **Beweiskette:** Separated inversion; not mere non-equality. **Review-Änderung:** proof detail. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 22. Modulated completeness characterization (theorem, main.tex:1171)

**Wortlaut der mathematischen Satzbehauptung:** For each base satisfying the ordered-field interface, the following are equivalent: \[\mathsf{UC}(K)\quad\Longleftrightarrow\quad\mathsf{CA}(K). \]

**Lean-Anker:** `TreeR.complete_iff_cauchyApprox`. **Beweiskette:** Only sequences supplied with a real Cauchy modulus. **Review-Änderung:** M03 TOField. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 23. Suprema from data (theorem, main.tex:1211)

**Wortlaut der mathematischen Satzbehauptung:** Given $D:\mathsf{SupData}(S)$, the rational bounds $u_k$ represent an element $\sup_D S\in\RR(K)$, which is a least upper bound of $S$ for the constructed real order.

**Lean-Anker:** `TreeR.SupData.isLUB`. **Beweiskette:** Approximation-bearing supremum; not arbitrary bounded subsets. **Review-Änderung:** proof detail. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 24. Logical equivalences; conditional form (theorem, main.tex:1282)

**Wortlaut der mathematischen Satzbehauptung:** For every base satisfying the project's ordered-field interface, the following exact forms are proved: \begin{align*} \bigl(\forall x\in\RR(K),\ x\ne0\Rightarrow\exists y,\ xy=1\bigr) &\quad\Longleftrightarrow\quad \mathsf{MP},\\ \bigl(\forall x\in\RR(K),\ x=0\ \lor\ x\Apt0\bigr) &\quad\Longleftrightarrow\quad \mathsf{LPO},\\ \mathsf{DecidableZero}(\RR(K))&\quad\Longleftrightarrow\quad\mathsf{WLPO}, \end{align*} with an additional source-specific equivalence between real trichotomy and LPO.

**Lean-Anker:** `TreeR.inv_iff_markov; TreeR.zeroOrApart_iff_lpo; TreeR.decidableZero_iff_wlpo; TreeR.trichotomy_iff_lpo`. **Beweiskette:** Correct conditional logical equivalences. **Review-Änderung:** M03 TOField. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.

## 25. One-way logical lower bounds (proposition, main.tex:1313)

**Wortlaut der mathematischen Satzbehauptung:** The source proves \[ \mathsf{UnrestrictedLUB}(K)\Longrightarrow\mathsf{WLPO},\qquad \mathsf{BoundedMonotoneConvergence}(K)\Longrightarrow\mathsf{LPO}. \]

**Lean-Anker:** `TreeR.wlpo_of_unrestrictedLUB; TreeR.lpo_of_bmc`. **Beweiskette:** Only one-way implications. **Review-Änderung:** none. **Prüfstatus:** Der archivierte Task-06-Build ist laut Claude lokal reproduziert; hier Source-Mapping, kein neuer Kernel-Lauf.


**Post-review refresh:** headings use the line numbers of the revised `main.tex`. Source references reflect `OmegaModule` and `Longitudinal` namespaces and independently cite `TreeQ.transfer_le` for arity order. The paragraphs originally extracted from the prior draft remain a navigation summary; the authoritative wording is the newly compiled `main.tex`.

## Mechanical crosswalk verification (long-form v2)

All 25 `main.tex:N` references above were regenerated from the actual start lines of the 11 theorem, 11 proposition, 2 lemma and 1 corollary environments in the delivered `main.tex`. See `MAIN_RESULT_PROOF_CHAINS.md` for the multi-step mathematical dependencies.
