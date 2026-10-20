(*  Title:      VWZ_Matrix.thy
    SPDX-License-Identifier: Apache-2.0

    VWZ A3 -- matrix / vector definition layer (definitions only).

    Scope: the linear-algebra objects referenced by the VWZ construction
    (spec Sec 4, 5.1, 6.4).  This file contains DEFINITIONS ONLY -- no lemma
    and no property is proved here; the matching obligations live in
    VWZ_ObligationsAligned (tiers T2/T3).

    Anchoring: imports VWZ_Fq3329 so the instance parameters (par_n, par_m,
    par_w) keep a single source of truth.

    Naming: the objects below carry a `mat_` prefix on purpose.  The
    placeholder constants in VWZ_ObligationsAligned (psi_slice, M2, ...) are
    typed over `nat list`; they are to be re-anchored onto this layer when T2
    starts, at which point those local placeholders get dropped.  Until then
    both spellings are inert -- no theory imports VWZ_Matrix.

    Bodies fixed by the spec text are given as real definitions; everything
    whose body needs rank / RREF machinery that is not yet formalised appears
    as an uninterpreted constant tagged TODO(define) with its spec section.
*)
theory VWZ_Matrix
  imports VWZ_Fq3329
begin

section \<open>Types\<close>

type_synonym vec = "int list"
type_synonym mat = "int list list"

section \<open>Structural definitions (fixed by the spec text)\<close>

definition n_rows :: "mat \<Rightarrow> nat" where
  "n_rows A = length A"

definition n_cols :: "mat \<Rightarrow> nat" where
  "n_cols A = (if A = [] then 0 else length (A ! 0))"

definition is_rect :: "mat \<Rightarrow> bool" where
  "is_rect A = (\<forall>r \<in> set A. length r = n_cols A)"

definition entry :: "mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int" where
  "entry A i j = A ! i ! j"

definition row_vec :: "mat \<Rightarrow> nat \<Rightarrow> vec" where
  "row_vec A i = A ! i"

definition col_vec :: "mat \<Rightarrow> nat \<Rightarrow> vec" where
  "col_vec A j = map (\<lambda>r. r ! j) A"

definition append_rows :: "mat \<Rightarrow> mat \<Rightarrow> mat" where
  "append_rows A B = A @ B"

definition vec_add :: "vec \<Rightarrow> vec \<Rightarrow> vec" where
  "vec_add u v = map2 (+) u v"

definition scalar_mul :: "int \<Rightarrow> vec \<Rightarrow> vec" where
  "scalar_mul c u = map ((*) c) u"

definition dot :: "vec \<Rightarrow> vec \<Rightarrow> int" where
  "dot u v = sum_list (map2 (*) u v)"

definition zero_mat :: "nat \<Rightarrow> nat \<Rightarrow> mat" where
  "zero_mat r c = replicate r (replicate c 0)"

text \<open>Identity and elementary matrices, and the product.  These bodies are
  fixed by the spec text (Sec 4, 6.4), so they are given as definitions here.
  `invertible` is the two-sided witness form, over a square of the row
  count; the general rank / solve questions stay deferred below.\<close>

definition id_mat :: "nat \<Rightarrow> mat" where
  "id_mat n = map (\<lambda>i. map (\<lambda>j. if i = j then 1 else 0) [0..<n]) [0..<n]"

definition mat_mult :: "mat \<Rightarrow> mat \<Rightarrow> mat" where
  "mat_mult A B =
     map (\<lambda>i. map (\<lambda>j. dot (row_vec A i) (col_vec B j)) [0..<n_cols B]) [0..<n_rows A]"

text \<open>Elementary row-addition matrix of size `m`: the identity with the
  factor `f` placed at (i, j).\<close>

definition row_add_matrix :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> mat" where
  "row_add_matrix m i j f =
     map (\<lambda>r. map (\<lambda>c. if r = i \<and> c = j then f else (if r = c then 1 else 0)) [0..<m]) [0..<m]"

definition invertible :: "mat \<Rightarrow> bool" where
  "invertible A =
     (\<exists>B. mat_mult A B = id_mat (n_rows A) \<and> mat_mult B A = id_mat (n_rows A))"

text \<open>2x2 determinant -- the Cramer helper of spec Sec 6.4, fixed by the text:\<close>

definition det2 :: "mat \<Rightarrow> int" where
  "det2 A = entry A 0 0 * entry A 1 1 - entry A 0 1 * entry A 1 0"

section \<open>VWZ matrix objects (2x2 bodies fixed here; general bodies deferred)\<close>

text \<open>Scalar inverse in Fq, by the Fermat exponent.  This is a DEFINITION
  choice only -- that it really is a multiplicative inverse is the property A7
  in VWZ_ObligationsAligned, not claimed here.\<close>

definition invmod :: "int \<Rightarrow> int" where
  "invmod a = (a ^ (3329 - (2::nat))) mod 3329"

text \<open>Rank predicates for the 2x2 slices used by the construction
  (spec Sec 4).  `mat_rank1` is "rank = 1", i.e. nonzero with proportional rows,
  which for a 2x2 matrix is exactly "det = 0 and not the zero matrix".\<close>

definition mat_rank1 :: "mat \<Rightarrow> bool" where
  "mat_rank1 A = (det2 A mod 3329 = 0 \<and> A \<noteq> zero_mat 2 2)"

definition mat_rank2 :: "mat \<Rightarrow> bool" where
  "mat_rank2 A = (det2 A mod 3329 \<noteq> 0)"

text \<open>Rank-2 row slice i (rows i and i+1).  `nth` is total in HOL, so no side
  condition is needed for the definition to be well-formed; the guard
  `i + 1 < n_rows A` is the intended reading at the use site.\<close>

definition mat_slice2 :: "mat \<Rightarrow> nat \<Rightarrow> mat" where
  "mat_slice2 A i = [A ! i, A ! (i + 1)]"

text \<open>Cramer solve of a 2x2 system (spec Sec 6.4.3, 2x2 case).  Returns
  None exactly when the determinant vanishes in Fq.\<close>

definition mat_solve2 :: "mat \<Rightarrow> vec \<Rightarrow> vec option" where
  "mat_solve2 A b =
     (if det2 A mod 3329 = 0 then None
      else Some [ (entry A 1 1 * b ! 0 - entry A 0 1 * b ! 1) * invmod (det2 A) mod 3329
                , (entry A 0 0 * b ! 1 - entry A 1 0 * b ! 0) * invmod (det2 A) mod 3329 ])"

text \<open>The nullspace as a SET of vectors (spec Sec 6.4.1).  Deliberately a
  predicate instead of an enumeration: Fq^2 has 3329^2 elements, so no
  computable basis enumeration is intended at this layer.\<close>

definition mat_nullspace :: "mat \<Rightarrow> vec set" where
  "mat_nullspace A =
     {v. length v = n_cols A \<and> (\<forall>i. i < n_rows A \<longrightarrow> dot (row_vec A i) v mod 3329 = 0)}"

text \<open>Frobenius (entrywise) inner product of two matrices (spec Sec 6.4.2).\<close>

definition mat_inner :: "mat \<Rightarrow> mat \<Rightarrow> int" where
  "mat_inner A B = sum_list (map2 dot A B)"

section \<open>Determinant (Laplace expansion)\<close>

text \<open>The general determinant is defined by Laplace expansion along the first
  row.  This choice is deliberate, and it is a definition-only choice: no
  property of the determinant is claimed in this file.

  Why not the Leibniz formula (the signed sum over all permutations)?  It is
  the textbook definition, and it is the one that makes multilinearity and
  alternation easiest to state, but it needs an enumeration of all
  permutations of the index set.  The Isabelle/HOL Permutations theory (in
  HOL-Combinatorics) defines permutes as a PREDICATE on functions, and sign
  on such functions; it deliberately provides no list-of-permutations
  enumerator.  Building one, and then proving it duplicate-free and complete,
  is a substantial development that would have to precede any use of the
  definition.  (Probed: the name is not in scope as a list former; the term
  is rejected as an illegal free variable.)

  Why not RREF?  Gaussian elimination needs a pivot search and division in
  F_q; the division is available (invmod), but the pivot argument -- that
  some entry in the remaining submatrix is nonzero, or else the determinant
  is zero -- is exactly the kind of reasoning the Laplace recursion gives
  for free.  RREF also computes a normal form rather than the determinant,
  so it would need an extra theorem to connect the two.

  Laplace expansion is total, needs no library beyond Main, and its
  recursion measure is plain length: deleting one row strictly decreases the
  row count.  Termination is therefore immediate.\<close>


text \<open>Delete column @{text j} from a row.\<close>

definition del_col :: "nat \<Rightarrow> int list \<Rightarrow> int list" where
  "del_col j r = take j r @ drop (Suc j) r"

text \<open>Determinant by Laplace expansion along the first row: the entry
  @{text "r ! j"} is multiplied by the determinant of the matrix obtained by
  deleting the first row and column @{text j}, and the sign alternates.
  The empty matrix has determinant 1 (the empty product), which makes the
  1x1 and 2x2 cases come out right.\<close>

function det :: "mat \<Rightarrow> int" where
  "det [] = 1"
| "det (r # rs) =
     sum_list (map (\<lambda>j. (-1) ^ j * r ! j * det (map (del_col j) rs))
                   [0..<length r])"
  by pat_completeness auto

termination det
  by (relation "measure length") auto

text \<open>The 3x3 case spelled out, as a cross-check and as a convenience for the
  obligations that only ever see 3x3 slices (spec Sec 4).  This is a derived
  definition, not an independent one: it is the Laplace expansion of a 3x3
  matrix with the recursion unrolled.  Its agreement with @{text det} on 3x3
  matrices is a lemma, not a definition, and is not claimed here.\<close>

definition det3 :: "mat \<Rightarrow> int" where
  "det3 A = entry A 0 0 * entry A 1 1 * entry A 2 2
          + entry A 0 1 * entry A 1 2 * entry A 2 0
          + entry A 0 2 * entry A 1 0 * entry A 2 1
          - entry A 0 2 * entry A 1 1 * entry A 2 0
          - entry A 0 1 * entry A 1 0 * entry A 2 2
          - entry A 0 0 * entry A 1 2 * entry A 2 1"

text \<open>Deferred: inverse and general Gauss-Jordan solve (the 2x2 bodies are
  det2 / mat_solve2 above).  Rank and nullspace dimension are no longer
  uninterpreted: they are defined from the RREF algorithm in
  \<open>VWZ_RREF\<close>, which is downstream of this file.\<close>

consts mat_inv :: "mat \<Rightarrow> mat"
       \<comment> \<open>TODO(define): spec Sec 6.4 -- for now only the 2x2 body (mat_solve2) exists\<close>

consts mat_solve :: "mat \<Rightarrow> vec \<Rightarrow> vec option"
       \<comment> \<open>TODO(define): spec Sec 6.4.3 -- general Gauss-Jordan solve\<close>

end
