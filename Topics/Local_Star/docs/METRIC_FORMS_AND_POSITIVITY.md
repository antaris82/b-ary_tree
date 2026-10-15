# Positive-definite, positive-semidefinite and identity forms: separate carriers

The historical study distinguished these forms. They must not be renamed into one "unit metric".

## 1. Full star Laplacian and DtN energy — positive SEMIdefinite
For the unit star with center `r` and children `i`:
```text
L = [ b    -1ᵀ ]
    [ -1    I  ]
E(U) = Σ_i (U_i-U_r)^2 ≥ 0.
```
Constant potentials lie in its nullspace; `E(U)=0` exactly for constants on the connected star. For a nonempty DtN boundary B, the reduced form `Uᵀ Λ_B U` is also PSD; its kernel is precisely the constant potentials **on B** when B is regarded as the actual retained carrier (singleton gives the zero form).

## 2. Grounded/relative form — positive definite
Fix one vertex's potential to zero, or pass to the quotient by constant potentials. The induced nonzero-relative energy is strictly positive. Do not assert PD on the unreduced full-potential space.

## 3. Resistance-derived Gram — identity and positive definite
For center-to-child resistance 1 and distinct child-to-child resistance 2, put:
```text
G_res(i,j) = (R(r,i)+R(r,j)-R(i,j))/2
           = δ(i,j).
```
Then `G_res = I_b`. For every nonzero `a` over the ordered Foundation rational field, `aᵀ G_res a = Σ a_i² > 0`. Here R is *squared Euclidean distance* in the edge-coordinate realization. The resistance matrix `[R(i,j)]` itself is **not** PSD in general.

## 4. Distinct coordinate Gram
In the full vertex-coordinate zero-sum space take `q_i = e_i-e_r`. With its standard coordinate dot product:
```text
G_coord(i,j) = δ(i,j)+1 = (I+J)(i,j).
```
Thus `G_coord ≠ G_res` for positive arity. On coefficients with `Σ_i a_i = 0`, the associated quadratic forms agree, because `aᵀ J a=(Σ_i a_i)²=0`. They differ on the longitudinal uniform direction. Do **not** identify the coordinate-dot form, the energy form and the resistance-polarization form without explicitly stating the carrier and the map.

## 5. Elimination of the center
For k retained children (`k>0`):
```text
Λ_P = I_k - (1/k)J_k.
```
This is a PSD projector with a constant null direction, NOT the identity matrix on all child coordinates. Its restriction to the sum-zero transverse subspace is the identity. Grounding or restricting appropriately yields PD, but the unreduced DtN form is never strictly PD when its retained carrier is nonempty.

## 6. Formalization gates
- Define all carriers, bilinear/quadratic forms and equality comparisons explicitly.
- Prove nonnegativity and exact nullspaces over `TOField`; no implicit Euclidean norm or square-root function.
- Prove identity Gram only after the two-terminal resistance equalities.
- Prove the transverse-restriction agreement, and show a longitudinal witness of non-agreement.
- Report exact Foundation interface and kernel status.

Status: mathematical formulas checked informally and with finite exact rational examples; **not** new-topic Lean theorems.
