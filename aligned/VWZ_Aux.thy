(*  Title:      VWZ_Aux.thy
    SPDX-License-Identifier: Apache-2.0

    VWZ A3 -- auxiliary lemmas (PROOF TOOLING, not obligations).

    Scope: helper lemmas that exist only to make the T1-D obligations
    provable.  They are deliberately kept OUT of VWZ_ObligationsAligned so
    that the obligation ledger (56 lemmas / 21 sorry as of 2026-10-19) stays
    a faithful count of OBLIGATIONS and is not inflated by proof machinery.
    _count.cjs scans only VWZ_ObligationsAligned.thy, so nothing here is ever
    counted.

    Rule: nothing in this file may be cited as evidence that an obligation is
    discharged.  If an aux lemma turns out to be an obligation in its own
    right, it must move to VWZ_ObligationsAligned and be counted.
*)
theory VWZ_Aux
  imports VWZ_Protocol
begin

section \<open>Arithmetic of the field modulus\<close>

text \<open>@{text "prime (3329::int)"} is not directly reachable by @{text simp}:
the library rule @{text "prime_nat_int_transfer"} is tagged @{text "[simp]"}
and the simplifier loops on it (observed: 240s CPU, no convergence).  The
route below avoids @{text simp} on a prime goal entirely.\<close>

lemma aux_prime_int: "prime (int 3329)"
  by (subst prime_nat_int_transfer) (rule prime_3329)

lemma aux_prime_int': "prime (3329::int)"
proof -
  have a: "prime (int 3329)" by (rule aux_prime_int)
  have b: "(3329::int) = int 3329" by presburger
  from a b show ?thesis by (metis)
qed

text \<open>Arithmetic core of obligation C6: over the field, multiplying by
  @{text "invmod x"} (for nonzero @{text x} in range) cannot create a zero.\<close>

lemma aux_c6_core:
  "0 \<le> t \<Longrightarrow> t < 3329 \<Longrightarrow> 1 \<le> x \<Longrightarrow> x < 3329 \<Longrightarrow>
    ((t * invmod x) mod 3329 = 0) = (t = 0)"
proof -
  assume h: "0 \<le> t" "t < 3329" "1 \<le> x" "x < 3329"
  have p: "prime (3329::int)" by (rule aux_prime_int')
  have xpos: "0 < x" using h(3) by simp
  have mm: "(t * invmod x) mod 3329 = (t * x ^ (3329 - 2)) mod 3329"
    by (simp add: invmod_def mod_mult_right_eq)
  have n2: "\<not> (3329 dvd x ^ (3329 - 2))"
  proof
    assume d: "3329 dvd x ^ (3329 - 2)"
    have dx: "3329 dvd x" using p d by (rule prime_dvd_power)
    have le: "3329 \<le> x" using dx xpos by (rule zdvd_imp_le)
    with h(4) show False by simp
  qed
  have key: "(3329 dvd t * x ^ (3329 - 2)) = (3329 dvd t)"
    using p n2 by (metis prime_dvd_mult_iff)
  have dvd0: "((t * x ^ (3329 - 2)) mod 3329 = 0) = (3329 dvd t * x ^ (3329 - 2))"
    by (simp add: mod_eq_0_iff_dvd)
  have t0: "(3329 dvd t) = (t = 0)"
  proof
    assume d: "3329 dvd t"
    show "t = 0"
    proof (rule ccontr)
      assume nz: "t \<noteq> 0"
      have tpos: "0 < t" using h(1) nz by simp
      have le: "3329 \<le> t" using d tpos by (rule zdvd_imp_le)
      with h(2) show False by simp
    qed
  next
    assume "t = 0" thus "3329 dvd t" by simp
  qed
  show ?thesis using mm dvd0 key t0 by simp
qed

section \<open>Serialization: u16 little-endian round-trip\<close>

text \<open>The pair-shift lemma is needed because @{text decode2} pairs bytes
  from index 0, so prepending two bytes shifts every later pair by one.  The
  library simplifier splits @{text "[0..<Suc n]"} into @{text "[0..<n] @ [n]"}
  (the wrong direction here); the split is therefore done explicitly with
  @{text map_upt_Suc}.\<close>

lemma aux_decode2_cons2:
  "even (length Y) \<Longrightarrow>
    decode2 (a # b # Y) = map_option (\<lambda>ys. (a + 256 * b) # ys) (decode2 Y)"
proof -
  assume ev: "even (length Y)"
  let ?g = "\<lambda>i. (a # b # Y) ! (2 * i) + 256 * (a # b # Y) ! (2 * i + 1)"
  let ?n = "length Y div 2"
  have len: "length (a # b # Y) = Suc (Suc (length Y))" by simp
  have ev2: "even (length (a # b # Y))" using ev len by simp
  have h: "length (a # b # Y) div 2 = Suc ?n" using ev len by simp
  have d: "decode2 (a # b # Y) = Some (map ?g [0..<Suc ?n])"
    using ev2 h by (simp add: decode2_def)
  have split: "map ?g [0..<Suc ?n] = ?g 0 # map (\<lambda>i. ?g (Suc i)) [0..<?n]"
    by (rule map_upt_Suc)
  have head: "?g 0 = a + 256 * b" by simp
  have tail: "map (\<lambda>i. ?g (Suc i)) [0..<?n]
                = map (\<lambda>i. Y ! (2 * i) + 256 * Y ! (2 * i + 1)) [0..<?n]"
    by (simp add: nth_Cons)
  have rhs: "map_option (\<lambda>ys. (a + 256 * b) # ys) (decode2 Y)
               = Some ((a + 256 * b) # map (\<lambda>i. Y ! (2 * i) + 256 * Y ! (2 * i + 1)) [0..<?n])"
    using ev by (simp add: decode2_def)
  show ?thesis using d split head tail rhs by simp
qed

lemma aux_u16le_roundtrip:
  "(\<forall>x\<in>set w. x < 65536) \<Longrightarrow> decode2 (concat (map u16le w)) = Some w"
proof (induction w)
  case Nil show ?case by (simp add: decode2_def)
next
  case (Cons a w)
  have hd: "a < 65536" using Cons.prems by simp
  have tl: "\<forall>x\<in>set w. x < 65536" using Cons.prems by simp
  have ev: "even (length (concat (map u16le w)))" by simp
  have eq: "u16le a @ concat (map u16le w)
              = (a mod 256) # ((a div 256) mod 256) # concat (map u16le w)"
    by (simp add: u16le_def)
  have H: "decode2 ((a mod 256) # ((a div 256) mod 256) # concat (map u16le w))
             = map_option (\<lambda>ys. (a mod 256 + 256 * ((a div 256) mod 256)) # ys)
                 (decode2 (concat (map u16le w)))"
    by (rule aux_decode2_cons2 [OF ev])
  have norm: "a mod 256 + 256 * ((a div 256) mod 256) = a"
  proof -
    have d1: "a div 256 mod 256 = a div 256" using hd by simp
    have d2: "a div 256 * 256 + a mod 256 = a" by (rule div_mult_mod_eq)
    have d3: "256 * (a div 256) = a div 256 * 256" by (rule mult.commute)
    show ?thesis using d1 d2 d3 by arith
  qed
  show ?case using Cons.IH [OF tl] eq H norm by simp
qed

section \<open>Determinant sanity checks (evidence, not obligations)\<close>

text \<open>The Laplace definition of @{text det} in VWZ_Matrix is new; these
  checks confirm that it computes the expected numbers on the cases the
  obligations actually mention (identity, elementary row addition, a known
  3x3).  They are evidence that the definition layer is self-consistent --
  they are NOT the obligation T2_B2, which asks for the general statement.\<close>

lemma aux_det_id3: "det (id_mat 3) = 1"
  by eval

lemma aux_det_rowadd3_01: "det (row_add_matrix 3 0 1 5) = 1"
  by eval

lemma aux_det_rowadd3_12: "det (row_add_matrix 3 1 2 (-3)) = 1"
  by eval

lemma aux_det_rowadd3_20: "det (row_add_matrix 3 2 0 7) = 1"
  by eval

lemma aux_det3_agrees:
  "det [[1,2,3],[4,5,6],[7,8,10]] = det3 [[1,2,3],[4,5,6],[7,8,10]]"
  by eval

lemma aux_det_id2: "det (id_mat 2) = 1"
  by eval

lemma aux_det_2x2_vs_det2: "det [[2,3],[5,7]] = det2 [[2,3],[5,7]]"
  by eval

section \<open>Determinant of the identity matrix (general n)\<close>

text \<open>Two facts learned the hard way:
  (a) @{term "[] ! 0"} is @{term undefined}, not a contradiction, so a
      @{term Nil} row cannot be ruled out from @{term "r ! 0 = 1"}.  The
      determinant lemma must therefore be stated for an explicit
      @{term "a # as"} row, and the caller supplies the length fact that
      rules out the empty row.
  (b) @{text "fix j"} leaves @{term j} polymorphic; when the hypothesis is
      later applied to @{term length}, unification fails with
      @{text "incompatible operand type"}.  Write @{text "fix j :: nat"}.<\<close>

lemma aux_sum_list_zero: "sum_list (replicate n (0::int)) = 0"
  by (induction n) simp_all

lemma aux_del_col_zero: "del_col 0 r = tl r"
  by (cases r) (simp_all add: del_col_def)

lemma aux_id_mat_nth:
  "k < n \<Longrightarrow> i < n \<Longrightarrow> id_mat n ! k ! i = (if k = i then (1::int) else 0)"
proof -
  assume "k < n"
  hence "id_mat n ! k = map (\<lambda>j. if k = j then (1::int) else 0) [0..<n]"
    by (simp add: id_mat_def)
  moreover assume "i < n"
  ultimately show ?thesis by simp
qed

lemma aux_id_mat_len: "length (id_mat n) = n"
  by (simp add: id_mat_def)

lemma aux_id_mat_row_len: "k < n \<Longrightarrow> length (id_mat n ! k) = n"
  by (simp add: id_mat_def)

lemma aux_tl_id_mat_len: "length (tl (id_mat (Suc m))) = m"
  by (simp add: aux_id_mat_len)

lemma aux_map_nth_id: "k < length xs \<Longrightarrow> map f xs ! k = f (xs ! k)"
  by (rule nth_map)

lemma aux_id_mat_decomp:
  "id_mat (Suc m) = (id_mat (Suc m) ! 0) # tl (id_mat (Suc m))"
proof (cases "id_mat (Suc m)")
  case Nil
  hence "length (id_mat (Suc m)) = 0" by simp
  moreover have "length (id_mat (Suc m)) = Suc m" by (simp add: aux_id_mat_len)
  ultimately show ?thesis by simp
next
  case (Cons r rs)
  have "r = id_mat (Suc m) ! 0" using Cons by simp
  thus ?thesis using Cons by simp
qed

lemma aux_delcol_tl_row:
  "k < m \<Longrightarrow> del_col 0 (tl (id_mat (Suc m)) ! k) = id_mat m ! k"
proof -
  assume km: "k < m"
  have row: "tl (id_mat (Suc m)) ! k = id_mat (Suc m) ! Suc k"
  proof (rule nth_tl)
    have "length (tl (id_mat (Suc m))) = m" by (rule aux_tl_id_mat_len)
    thus "k < length (tl (id_mat (Suc m)))" using km by simp
  qed
  have rowlen: "length (tl (id_mat (Suc m)) ! k) = Suc m"
  proof -
    have sk: "Suc k < Suc m" using km by simp
    have "length (id_mat (Suc m) ! Suc k) = Suc m" by (rule aux_id_mat_row_len) (rule sk)
    with row show ?thesis by simp
  qed
  have dellen: "length (del_col 0 (tl (id_mat (Suc m)) ! k)) = m"
  proof -
    have "del_col 0 (tl (id_mat (Suc m)) ! k) = tl (tl (id_mat (Suc m)) ! k)"
      by (rule aux_del_col_zero)
    hence "length (del_col 0 (tl (id_mat (Suc m)) ! k))
         = length (tl (tl (id_mat (Suc m)) ! k))" by simp
    moreover have "length (tl (tl (id_mat (Suc m)) ! k)) = m" using rowlen by simp
    ultimately show ?thesis by simp
  qed
  show ?thesis
  proof (rule nth_equalityI)
    show "length (del_col 0 (tl (id_mat (Suc m)) ! k)) = length (id_mat m ! k)"
      using dellen km aux_id_mat_row_len by simp
  next
    fix i
    assume i: "i < length (del_col 0 (tl (id_mat (Suc m)) ! k))"
    have im: "i < m" using dellen i by simp
    have si: "Suc i < Suc m" using im by simp
    have sk: "Suc k < Suc m" using km by simp
    have a: "del_col 0 (tl (id_mat (Suc m)) ! k) ! i
           = tl (tl (id_mat (Suc m)) ! k) ! i"
      by (simp add: aux_del_col_zero)
    have b: "\<dots> = (tl (id_mat (Suc m)) ! k) ! Suc i"
    proof (rule nth_tl)
      show "i < length (tl (tl (id_mat (Suc m)) ! k))" using rowlen im by simp
    qed
    have c: "\<dots> = (id_mat (Suc m) ! Suc k) ! Suc i"
      using row by simp
    have e: "\<dots> = (if Suc k = Suc i then (1::int) else 0)"
      by (rule aux_id_mat_nth) (rule sk, rule si)
    have f: "\<dots> = (if k = i then (1::int) else 0)" by simp
    have g: "id_mat m ! k ! i = (if k = i then (1::int) else 0)"
      by (rule aux_id_mat_nth) (rule km, rule im)
    show "del_col 0 (tl (id_mat (Suc m)) ! k) ! i = id_mat m ! k ! i"
      using a b c e f g by simp
  qed
qed

lemma aux_delcol_tl_id_mat:
  "map (del_col 0) (tl (id_mat (Suc m))) = id_mat m"
proof (rule nth_equalityI)
  have tl_len: "length (tl (id_mat (Suc m))) = m" by (rule aux_tl_id_mat_len)
  show "length (map (del_col 0) (tl (id_mat (Suc m)))) = length (id_mat m)"
    using tl_len aux_id_mat_len by simp
next
  fix k
  assume k: "k < length (map (del_col 0) (tl (id_mat (Suc m))))"
  have tl_len: "length (tl (id_mat (Suc m))) = m" by (rule aux_tl_id_mat_len)
  have km: "k < m" using k tl_len by simp
  have kmap: "map (del_col 0) (tl (id_mat (Suc m))) ! k
            = del_col 0 (tl (id_mat (Suc m)) ! k)"
    by (rule aux_map_nth_id) (use km tl_len in simp)
  have "del_col 0 (tl (id_mat (Suc m)) ! k) = id_mat m ! k"
    by (rule aux_delcol_tl_row) (rule km)
  with kmap show "map (del_col 0) (tl (id_mat (Suc m))) ! k = id_mat m ! k" by simp
qed

lemma aux_sum_head_collapse:
  assumes h: "\<And>j. 0 < (j::nat) \<Longrightarrow> j < Suc m \<Longrightarrow> g j = (0::int)"
  shows "sum_list (map g [0..<Suc m]) = g 0"
proof -
  have m1: "map g [0..<Suc m] = g 0 # map (\<lambda>i. g (Suc i)) [0..<m]"
    by (rule map_upt_Suc)
  have m2: "map (\<lambda>i. g (Suc i)) [0..<m] = replicate m 0"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>i. g (Suc i)) [0..<m]) = length (replicate m 0)" by simp
  next
    fix i
    assume "i < length (map (\<lambda>i. g (Suc i)) [0..<m])"
    hence im: "i < m" by simp
    have "g (Suc i) = (0::int)" using h im by simp
    thus "map (\<lambda>i. g (Suc i)) [0..<m] ! i = replicate m 0 ! i" using im by simp
  qed
  have a: "sum_list (map g [0..<Suc m]) = sum_list (g 0 # map (\<lambda>i. g (Suc i)) [0..<m])"
    by (simp only: m1)
  have b: "sum_list (g 0 # map (\<lambda>i. g (Suc i)) [0..<m]) = sum_list (g 0 # replicate m 0)"
    by (simp only: m2)
  have c: "sum_list (g 0 # replicate m 0) = g 0" by (simp add: aux_sum_list_zero)
  show ?thesis using a b c by simp
qed

text \<open>Stated for an explicit @{term "a # as"} row -- see note (a) above.<\<close>

lemma aux_det_head_one_cons:
  assumes h1: "a = (1::int)"
  and h2: "\<And>j. 0 < (j::nat) \<Longrightarrow> j < Suc (length as) \<Longrightarrow> as ! (j - Suc 0) = (0::int)"
  shows "det ((a # as) # rs) = det (map (del_col 0) rs)"
proof -
  have len: "length (a # as) = Suc (length as)" by simp
  have unfold: "det ((a # as) # rs) =
      sum_list (map (\<lambda>j. (-1) ^ j * (a # as) ! j * det (map (del_col j) rs))
                [0..<Suc (length as)])"
  proof -
    have "det ((a # as) # rs) =
          sum_list (map (\<lambda>j. (-1) ^ j * (a # as) ! j * det (map (del_col j) rs))
                    [0..<length (a # as)])"
      by (simp add: det.simps(2))
    thus ?thesis using len by simp
  qed
  have gz: "\<And>j. 0 < (j::nat) \<Longrightarrow> j < Suc (length as) \<Longrightarrow>
            ((-1) ^ j * (a # as) ! j * det (map (del_col j) rs)) = (0::int)"
  proof -
    fix j :: nat
    assume j1: "0 < j" and j2: "j < Suc (length as)"
    have eq: "j = Suc (j - Suc 0)" using j1 by arith
    have "(a # as) ! j = as ! (j - Suc 0)" using eq by simp
    moreover have "as ! (j - Suc 0) = (0::int)" by (rule h2) (rule j1, rule j2)
    ultimately have "(a # as) ! j = (0::int)" by simp
    thus "(-1) ^ j * (a # as) ! j * det (map (del_col j) rs) = (0::int)" by simp
  qed
  have collapse:
    "sum_list (map (\<lambda>j. (-1) ^ j * (a # as) ! j * det (map (del_col j) rs))
                [0..<Suc (length as)])
     = (-1) ^ (0::nat) * (a # as) ! 0 * det (map (del_col 0) rs)"
    by (rule aux_sum_head_collapse) (rule gz)
  have simp0: "(-1) ^ (0::nat) * (a # as) ! 0 * det (map (del_col 0) rs)
             = det (map (del_col 0) rs)"
    using h1 by simp
  have "det ((a # as) # rs) = det (map (del_col 0) rs)"
    using unfold collapse simp0 by simp
  thus ?thesis .
qed

lemma aux_det_id_mat: "det (id_mat n) = 1"
proof (induction n)
  case 0
  show ?case by (simp add: id_mat_def)
next
  case (Suc m)
  have ih: "det (id_mat m) = 1" using Suc.IH .
  have dec: "id_mat (Suc m) = (id_mat (Suc m) ! 0) # tl (id_mat (Suc m))"
    by (rule aux_id_mat_decomp)
  have len0: "length (id_mat (Suc m) ! 0) = Suc m" by (simp add: aux_id_mat_row_len)
  show ?case
  proof (cases "id_mat (Suc m) ! 0")
    case Nil
    hence "Suc m = 0" using len0 by simp
    thus ?thesis by simp
  next
    case (Cons a as)
    have a1: "a = (1::int)"
    proof -
      have "(id_mat (Suc m) ! 0) ! 0 = a" using Cons by simp
      moreover have "(id_mat (Suc m) ! 0) ! 0 = (1::int)" by (simp add: aux_id_mat_nth)
      ultimately show ?thesis by simp
    qed
    have asz: "\<And>j. 0 < (j::nat) \<Longrightarrow> j < Suc (length as) \<Longrightarrow>
               as ! (j - Suc 0) = (0::int)"
    proof -
      fix j :: nat
      assume j1: "0 < j" and j2: "j < Suc (length as)"
      have rowlen: "length (id_mat (Suc m) ! 0) = Suc (length as)"
        using Cons len0 by simp
      have jl: "j < Suc m" using j2 rowlen len0 by simp
      have "(id_mat (Suc m) ! 0) ! j = (if 0 = j then (1::int) else 0)"
        by (simp add: aux_id_mat_nth jl)
      hence "(id_mat (Suc m) ! 0) ! j = (0::int)" using j1 by simp
      moreover have "(id_mat (Suc m) ! 0) ! j = as ! (j - Suc 0)"
      proof -
        have eq: "j = Suc (j - Suc 0)" using j1 by arith
        with Cons show ?thesis by simp
      qed
      ultimately show "as ! (j - Suc 0) = (0::int)" by simp
    qed
    have step: "det (id_mat (Suc m)) = det (map (del_col 0) (tl (id_mat (Suc m))))"
    proof -
      have e1: "det (id_mat (Suc m)) = det ((a # as) # tl (id_mat (Suc m)))"
        using dec Cons by simp
      have e2: "det ((a # as) # tl (id_mat (Suc m)))
               = det (map (del_col 0) (tl (id_mat (Suc m))))"
        by (rule aux_det_head_one_cons) (rule a1, rule asz)
      show ?thesis using e1 e2 by simp
    qed
    have "det (id_mat (Suc m)) = det (id_mat m)"
      using step aux_delcol_tl_id_mat by simp
    also have "\<dots> = 1" by (rule ih)
    finally show ?thesis .
  qed
qed

section \<open>Multilinearity of the Laplace determinant (first row)\<close>

lemma aux_det_head_zero: "det (replicate m 0 # rs) = (0::int)"
proof -
  have unfold: "det (replicate m 0 # rs) =
      sum_list (map (\<lambda>j. (-1) ^ j * (replicate m 0) ! j * det (map (del_col j) rs))
                [0..<length (replicate m 0)])"
    by (simp add: det.simps(2))
  have len: "length (replicate m 0 :: int list) = m" by simp
  have zeroes: "map (\<lambda>j. (-1) ^ j * (replicate m 0) ! j * det (map (del_col j) rs))
                [0..<m] = replicate m (0::int)"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>j. (-1) ^ j * (replicate m 0) ! j * det (map (del_col j) rs)) [0..<m])
        = length (replicate m (0::int))" by simp
  next
    fix j
    assume "j < length (map (\<lambda>j. (-1) ^ j * (replicate m 0) ! j * det (map (del_col j) rs)) [0..<m])"
    hence jm: "j < m" by simp
    have z: "(replicate m 0 :: int list) ! j = (0::int)" using jm by simp
    thus "map (\<lambda>j. (-1) ^ j * (replicate m 0) ! j * det (map (del_col j) rs)) [0..<m] ! j
        = replicate m (0::int) ! j"
      using jm z by simp
  qed
  show ?thesis using unfold len zeroes aux_sum_list_zero by simp
qed

lemma aux_det_head_add:
  assumes len: "length a = length b"
  shows "det ((map2 (+) a b) # rs) = det (a # rs) + det (b # rs)"
proof -
  have lab: "length (map2 (+) a b :: int list) = length a" using len by simp
  have unfold_a: "det (a # rs) =
      sum_list (map (\<lambda>j. (-1) ^ j * a ! j * det (map (del_col j) rs)) [0..<length a])"
    by (simp add: det.simps(2))
  have unfold_b: "det (b # rs) =
      sum_list (map (\<lambda>j. (-1) ^ j * b ! j * det (map (del_col j) rs)) [0..<length b])"
    by (simp add: det.simps(2))
  have unfold_ab: "det ((map2 (+) a b) # rs) =
      sum_list (map (\<lambda>j. (-1) ^ j * (map2 (+) a b) ! j * det (map (del_col j) rs))
                [0..<length (map2 (+) a b)])"
    by (simp add: det.simps(2))
  have step: "map (\<lambda>j. (-1) ^ j * (map2 (+) a b) ! j * det (map (del_col j) rs)) [0..<length a]
            = map (\<lambda>j. (-1) ^ j * a ! j * det (map (del_col j) rs)
                   + (-1) ^ j * b ! j * det (map (del_col j) rs)) [0..<length a]"
  proof (rule map_cong [OF refl])
    fix j
    assume j: "j \<in> set [0..<length a]"
    hence jl: "j < length a" by simp
    have nth: "(map2 (+) a b :: int list) ! j = a ! j + b ! j" using len jl by simp
    thus "(-1) ^ j * (map2 (+) a b) ! j * det (map (del_col j) rs)
        = (-1) ^ j * a ! j * det (map (del_col j) rs)
          + (-1) ^ j * b ! j * det (map (del_col j) rs)"
      using nth by (simp add: algebra_simps)
  qed
  have split: "sum_list (map (\<lambda>j. (-1) ^ j * a ! j * det (map (del_col j) rs)
                   + (-1) ^ j * b ! j * det (map (del_col j) rs)) [0..<length a])
             = sum_list (map (\<lambda>j. (-1) ^ j * a ! j * det (map (del_col j) rs)) [0..<length a])
             + sum_list (map (\<lambda>j. (-1) ^ j * b ! j * det (map (del_col j) rs)) [0..<length a])"
    by (rule sum_list_addf)
  show ?thesis
  proof -
    have "det ((map2 (+) a b) # rs)
        = sum_list (map (\<lambda>j. (-1) ^ j * (map2 (+) a b) ! j * det (map (del_col j) rs))
                    [0..<length a])"
      using unfold_ab lab by simp
    also have "\<dots> = sum_list (map (\<lambda>j. (-1) ^ j * a ! j * det (map (del_col j) rs)
                    + (-1) ^ j * b ! j * det (map (del_col j) rs)) [0..<length a])"
      by (simp only: step)
    also have "\<dots> = det (a # rs) + det (b # rs)"
      using unfold_a unfold_b len split by simp
    finally show ?thesis .
  qed
qed


text \<open>All-zero row implies vanishing determinant.

  Induction is on length M, not on the list structure: the recursive step needs
  the hypothesis at map (del_col j) rs, which is not a structural subterm of
  r # rs, so structural induction cannot reach it.  Squareness is not required.

  Three Isar pitfalls had to be worked around, all confirmed by isolated probes:
  (1) length_induct needs a term-level goal P M, so the lemma must be stated
      with --> or proved via nat_less_induct with arbitrary: M;
  (2) with arbitrary: M the outer show ?case has a schematic ?M, so ?thesis
      inside nested cases resolves to that schematic form and leaves an
      unclosable goal -- state det M = 0 explicitly instead;
  (3) "using eq by simp" treats eq as a rewrite rule and spawns side goals --
      use arg_cong[OF eq] to rewrite under sum_list.\<close>

definition zrow :: "int list \<Rightarrow> bool" where
  "zrow r = (\<forall>j. j < length r \<longrightarrow> r ! j = 0)"

definition zhas :: "mat \<Rightarrow> bool" where
  "zhas M = (\<exists>r \<in> set M. zrow r)"

lemma aux_zrow_iff: "zrow r = (\<forall>x \<in> set r. x = (0::int))"
proof -
  have a: "zrow r \<Longrightarrow> (\<forall>x \<in> set r. x = (0::int))"
    by (auto simp add: zrow_def in_set_conv_nth)
  have b: "(\<forall>x \<in> set r. x = (0::int)) \<Longrightarrow> zrow r"
  proof -
    assume h: "\<forall>x \<in> set r. x = (0::int)"
    have "\<And>j. j < length r \<Longrightarrow> r ! j = (0::int)"
    proof -
      fix j
      assume j: "j < length r"
      have "r ! j \<in> set r" using j by (rule nth_mem)
      with h show "r ! j = (0::int)" by simp
    qed
    thus "zrow r" by (simp add: zrow_def)
  qed
  from a b show ?thesis by blast
qed

lemma aux_zrow_replicate:
  assumes "zrow r"
  shows "r = replicate (length r) (0::int)"
  using assms by (simp add: zrow_def list_eq_iff_nth_eq)

lemma aux_zrow_del_col:
  assumes z: "zrow r"
  shows "zrow (del_col j r)"
proof -
  have sub: "set (del_col j r) \<subseteq> set r"
    by (simp add: del_col_def set_take_subset set_drop_subset)
  have allz: "\<forall>x \<in> set r. x = (0::int)" using z by (simp add: aux_zrow_iff)
  have "\<forall>x \<in> set (del_col j r). x = (0::int)" using sub allz by blast
  thus ?thesis by (simp add: aux_zrow_iff)
qed

lemma aux_zhas_map_del_col:
  assumes "zhas rs"
  shows "zhas (map (del_col j) rs)"
proof -
  from assms obtain r where r: "r \<in> set rs" "zrow r" by (auto simp add: zhas_def)
  have mem: "del_col j r \<in> set (map (del_col j) rs)" using r(1) by simp
  have zr: "zrow (del_col j r)" using r(2) by (rule aux_zrow_del_col)
  show ?thesis using mem zr by (auto simp add: zhas_def)
qed

lemma aux_det_zero_row:
  assumes "zhas M"
  shows "det M = (0::int)"
  using assms
proof (induct "length M" arbitrary: M rule: nat_less_induct)
  case (1 M)
  have IH: "\<And>N. length N < length M \<Longrightarrow> zhas N \<Longrightarrow> det N = (0::int)" using 1 by blast
  have zM: "zhas M" using 1 by blast
  show ?case
  proof (cases M)
    case Nil
    then show ?thesis using zM by (simp add: zhas_def)
  next
    case (Cons r rs)
    note M_eq = this
    have zM': "zhas (r # rs)" using zM M_eq by simp
    show ?thesis
    proof (cases "zrow r")
      case True
      have rr: "r = replicate (length r) (0::int)" using True by (rule aux_zrow_replicate)
      have h1a: "det (r # rs) = det (replicate (length r) (0::int) # rs)"
        using rr by simp
      have h1b: "det (replicate (length r) (0::int) # rs) = (0::int)"
        by (rule aux_det_head_zero)
      have h1: "det (r # rs) = (0::int)" using h1a h1b by simp
      show ?thesis using M_eq h1 by simp
    next
      case False
      have zrs: "zhas rs" using zM' False by (auto simp add: zhas_def)
      have zero_cofs: "\<And>j. j < length r \<Longrightarrow> det (map (del_col j) rs) = (0::int)"
      proof -
        fix j
        assume j_lt: "j < length r"
        have len_less: "length (map (del_col j) rs) < length M" using M_eq j_lt by simp
        have z: "zhas (map (del_col j) rs)" using zrs by (rule aux_zhas_map_del_col)
        show "det (map (del_col j) rs) = (0::int)" using IH[OF len_less z] .
      qed
      have eq: "map (\<lambda>j. (-1) ^ j * r ! j * det (map (del_col j) rs)) [0..<length r]
                = map (\<lambda>_. (0::int)) [0..<length r]"
      proof (rule map_cong)
        show "[0..<length r] = [0..<length r]" by simp
      next
        fix j
        assume "j \<in> set [0..<length r]"
        then have j: "j < length r" by simp
        with zero_cofs show "(-1) ^ j * r ! j * det (map (del_col j) rs) = (0::int)" by simp
      qed
      have lap: "det (r # rs)
                 = sum_list (map (\<lambda>j. (-1) ^ j * r ! j * det (map (del_col j) rs)) [0..<length r])"
        by (simp add: det.simps)
      have z0': "sum_list (map (\<lambda>j. (-1) ^ j * r ! j * det (map (del_col j) rs)) [0..<length r])
                 = (0::int)"
      proof -
        have "sum_list (map (\<lambda>j. (-1) ^ j * r ! j * det (map (del_col j) rs)) [0..<length r])
              = sum_list (map (\<lambda>_. (0::int)) [0..<length r])"
          by (rule arg_cong[OF eq])
        also have "\<dots> = (0::int)" by simp
        finally show ?thesis .
      qed
      have h2: "det (r # rs) = (0::int)" using lap z0' by simp
      show ?thesis using M_eq h2 by simp
    qed
  qed
qed
(* seg: aux-det-zero-row-20261019 *)

(* seg: aux-det-elementary-i0-20261019 *)
text \<open>--- A: arithmetic on replicate blocks ---\<close>
lemma aux_el_replicate_split:
  assumes k: "0 < k" and km: "k < m"
  shows "replicate k (0::int) @ replicate (m - Suc k) 0 = replicate (m - 1) 0"
proof (rule nth_equalityI)
  show "length (replicate k (0::int) @ replicate (m - Suc k) 0) = length (replicate (m - 1) 0)"
    using k km by simp
next
  fix i
  assume i: "i < length (replicate k (0::int) @ replicate (m - Suc k) 0)"
  show "(replicate k (0::int) @ replicate (m - Suc k) 0) ! i = replicate (m - 1) 0 ! i"
    using i k km by (simp add: nth_append)
qed

text \<open>--- B: the left zero block ---\<close>
lemma aux_el_zero_left:
  "map (\<lambda>c. if k = c then (1::int) else 0) [0..<k] = replicate k 0"
proof (rule nth_equalityI)
  show "length (map (\<lambda>c. if k = c then (1::int) else 0) [0..<k]) = length (replicate k 0)"
    by simp
next
  fix i
  assume i: "i < length (map (\<lambda>c. if k = c then (1::int) else 0) [0..<k])"
  hence ik: "i < k" by simp
  have h1: "map (\<lambda>c. if k = c then (1::int) else 0) [0..<k] ! i = (if k = i then (1::int) else 0)"
    using ik by (simp add: nth_map nth_upt)
  have h2: "k \<noteq> i" using ik by simp
  have h3: "replicate k (0::int) ! i = (0::int)" using ik by simp
  show "map (\<lambda>c. if k = c then (1::int) else 0) [0..<k] ! i = replicate k 0 ! i"
    using h1 h2 h3 by simp
qed

text \<open>--- C: the right zero block ---\<close>
lemma aux_el_zero_right:
  "map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m] = replicate (m - Suc k) 0"
proof (rule nth_equalityI)
  show "length (map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m]) = length (replicate (m - Suc k) 0)"
    by simp
next
  fix i
  assume i: "i < length (map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m])"
  have h1: "map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m] ! i
          = (if k = [Suc k..<m] ! i then (1::int) else 0)"
    using i by (simp add: nth_map nth_upt)
  have h2: "[Suc k..<m] ! i = Suc k + i" using i by (simp add: nth_upt)
  have h3: "k \<noteq> Suc k + i" by simp
  have h4: "replicate (m - Suc k) (0::int) ! i = (0::int)" using i by simp
  show "map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m] ! i = replicate (m - Suc k) 0 ! i"
    using h1 h2 h3 h4 by simp
qed

text \<open>--- D: deleting column k from the unit row e_k gives zeros ---\<close>
lemma aux_el_delcol_unit:
  assumes k1: "0 < k" and k2: "k < m"
  shows "del_col k (map (\<lambda>c. if k = c then (1::int) else 0) [0..<m]) = replicate (m - 1) 0"
proof -
  have dc: "del_col k r = take k r @ drop (Suc k) r" for r :: "int list"
    by (simp add: del_col_def)
  have t1: "take k (map (\<lambda>c. if k = c then (1::int) else 0) [0..<m])
          = map (\<lambda>c. if k = c then (1::int) else 0) [0..<k]"
    using k2 by (simp add: take_map take_upt)
  have t2: "drop (Suc k) (map (\<lambda>c. if k = c then (1::int) else 0) [0..<m])
          = map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m]"
    by (simp add: drop_map drop_upt)
  have t3: "map (\<lambda>c. if k = c then (1::int) else 0) [0..<k] = replicate k 0"
    by (rule aux_el_zero_left)
  have t4: "map (\<lambda>c. if k = c then (1::int) else 0) [Suc k..<m] = replicate (m - Suc k) 0"
    by (rule aux_el_zero_right)
  have t5: "replicate k (0::int) @ replicate (m - Suc k) 0 = replicate (m - 1) 0"
    by (rule aux_el_replicate_split) (rule k1, rule k2)
  show ?thesis using dc t1 t2 t3 t4 t5 by simp
qed

text \<open>--- E: row 0 of E ---\<close>
lemma aux_el_row0:
  assumes m0: "0 < m"
  shows "hd (row_add_matrix m 0 jc f)
       = map (\<lambda>c. if c = jc then f else (if c = 0 then (1::int) else 0)) [0..<m]"
proof -
  have h: "row_add_matrix m 0 jc f
      = map (\<lambda>r. map (\<lambda>c. if r = 0 \<and> c = jc then f else (if r = c then (1::int) else 0)) [0..<m]) [0..<m]"
    by (simp add: row_add_matrix_def)
  have s: "[0..<m] = 0 # [Suc 0..<m]"
    by (rule upt_conv_Cons) (simp add: m0)
  show ?thesis using h s by simp
qed

text \<open>--- F: the tail of E is the tail of the identity ---\<close>
lemma aux_el_tl:
  assumes m0: "0 < m"
  shows "tl (row_add_matrix m 0 jc f) = tl (id_mat m)"
proof -
  have h: "row_add_matrix m 0 jc f
      = map (\<lambda>r. map (\<lambda>c. if r = 0 \<and> c = jc then f else (if r = c then (1::int) else 0)) [0..<m]) [0..<m]"
    by (simp add: row_add_matrix_def)
  have s: "[0..<m] = 0 # [Suc 0..<m]"
    by (rule upt_conv_Cons) (simp add: m0)
  show ?thesis using h s by (simp add: id_mat_def)
qed

text \<open>--- G: length of the identity tail ---\<close>
lemma aux_el_tl_id_mat_len:
  assumes m0: "0 < m"
  shows "length (tl (id_mat m)) = m - 1"
proof -
  have len: "length (id_mat m) = m" by (rule aux_id_mat_len)
  have ne: "id_mat m \<noteq> []"
  proof
    assume "id_mat m = []"
    hence "length (id_mat m) = 0" by simp
    thus False using len m0 by simp
  qed
  have "length (tl (id_mat m)) = length (id_mat m) - 1" using ne by simp
  thus ?thesis using len by simp
qed

text \<open>--- G2: shifting a unit row by one index ---\<close>
lemma aux_el_shift_unit:
  "map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m]
   = map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1]"
proof (rule nth_equalityI)
  show "length (map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m])
      = length (map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1])"
    by simp
next
  fix c
  assume c: "c < length (map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m])"
  have h1: "map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m] ! c
          = (if Suc i = [Suc 0..<m] ! c then (1::int) else 0)"
    using c by (simp add: nth_map nth_upt)
  have h2: "[Suc 0..<m] ! c = Suc 0 + c" using c by (simp add: nth_upt)
  have h3: "Suc i = Suc 0 + c \<longleftrightarrow> i = c" by simp
  have h4: "map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1] ! c
          = (if i = [0..<m - 1] ! c then (1::int) else 0)"
    using c by (simp add: nth_map nth_upt)
  have h5: "[0..<m - 1] ! c = c" using c by (simp add: nth_upt)
  show "map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m] ! c
      = map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1] ! c"
    using h1 h2 h3 h4 h5 by simp
qed

text \<open>--- H: the (0,0) minor of E is the identity of size m-1 ---\<close>
lemma aux_el_minor0:
  assumes m0: "0 < m"
  shows "map (del_col 0) (tl (row_add_matrix m 0 jc f)) = id_mat (m - 1)"
proof -
  have a: "tl (row_add_matrix m 0 jc f) = tl (id_mat m)" by (rule aux_el_tl) (rule m0)
  have b: "map (del_col 0) (tl (id_mat m)) = id_mat (m - 1)"
  proof (rule nth_equalityI)
    have tl_len: "length (tl (id_mat m)) = m - 1" by (rule aux_el_tl_id_mat_len) (rule m0)
    show "length (map (del_col 0) (tl (id_mat m))) = length (id_mat (m - 1))"
      using tl_len aux_id_mat_len by simp
  next
    fix i
    have tl_len: "length (tl (id_mat m)) = m - 1" by (rule aux_el_tl_id_mat_len) (rule m0)
    assume i: "i < length (map (del_col 0) (tl (id_mat m)))"
    hence im: "i < m - 1" using tl_len by simp
    have sc: "i < length (tl (id_mat m))" using i by simp
    have r1: "map (del_col 0) (tl (id_mat m)) ! i = del_col 0 (tl (id_mat m) ! i)"
      using i by (simp add: nth_map)
    have r2: "del_col 0 (tl (id_mat m) ! i) = tl (tl (id_mat m) ! i)"
      by (simp add: aux_del_col_zero)
    have r3a: "tl (id_mat m) ! i = id_mat m ! Suc i"
      by (rule nth_tl) (rule sc)
    have r3: "tl (tl (id_mat m) ! i) = tl (id_mat m ! Suc i)" using r3a by simp
    have r4: "tl (id_mat m ! Suc i) = map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1]"
    proof -
      have row: "id_mat m ! Suc i = map (\<lambda>j. if Suc i = j then (1::int) else 0) [0..<m]"
        using im by (simp add: id_mat_def nth_map)
      have s: "[0..<m] = 0 # [Suc 0..<m]"
        by (rule upt_conv_Cons) (simp add: m0)
      have e: "tl (map (\<lambda>j. if Suc i = j then (1::int) else 0) [0..<m])
             = map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m]"
        using s by simp
      have f: "map (\<lambda>j. if Suc i = j then (1::int) else 0) [Suc 0..<m]
             = map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1]"
        by (rule aux_el_shift_unit)
      show ?thesis using row e f by simp
    qed
    have r5: "map (\<lambda>j. if i = j then (1::int) else 0) [0..<m - 1] = id_mat (m - 1) ! i"
      using im by (simp add: id_mat_def nth_map)
    show "map (del_col 0) (tl (id_mat m)) ! i = id_mat (m - 1) ! i"
      using r1 r2 r3 r4 r5 by simp
  qed
  show ?thesis using a b by simp
qed

text \<open>--- I: variable-bound version of the head collapse ---\<close>
lemma aux_el_collapse_var:
  assumes m0: "0 < m"
  and h: "\<And>k. 0 < (k::nat) \<Longrightarrow> k < m \<Longrightarrow> g k = (0::int)"
  shows "sum_list (map g [0..<m]) = g 0"
proof -
  have a: "sum_list (map g [0..<Suc (m - 1)]) = g 0"
  proof (rule aux_sum_head_collapse)
    fix j :: nat
    assume j1: "0 < j" and j2: "j < Suc (m - 1)"
    show "g j = (0::int)"
    proof (rule h)
      show "0 < j" by (rule j1)
      show "j < m" using j2 m0 by simp
    qed
  qed
  have eq: "m = Suc (m - 1)" using m0 by simp
  show ?thesis using a eq by simp
qed

text \<open>--- J: the zero-row witness in the tail of E ---\<close>
lemma aux_el_tail_zhas:
  assumes j1: "0 < jc" and j2: "jc < m" and m0: "0 < m"
  shows "zhas (map (del_col jc) (tl (row_add_matrix m 0 jc f)))"
proof -
  have tl_eq: "tl (row_add_matrix m 0 jc f) = tl (id_mat m)" by (rule aux_el_tl) (rule m0)
  have tl_len: "length (tl (id_mat m)) = m - 1" by (rule aux_el_tl_id_mat_len) (rule m0)
  have jm: "jc - 1 < m - 1" using j1 j2 by simp
  have sc: "jc - 1 < length (tl (id_mat m))" using tl_len jm by simp
  have row_at: "tl (id_mat m) ! (jc - 1) = id_mat m ! jc"
  proof -
    have a: "tl (id_mat m) ! (jc - 1) = id_mat m ! Suc (jc - 1)"
      by (rule nth_tl) (rule sc)
    have b: "Suc (jc - 1) = jc" using j1 by simp
    show ?thesis using a b by simp
  qed
  have row_in: "id_mat m ! jc \<in> set (tl (id_mat m))"
  proof -
    have "tl (id_mat m) ! (jc - 1) \<in> set (tl (id_mat m))" by (rule nth_mem) (rule sc)
    thus ?thesis using row_at by simp
  qed
  have zr: "zrow (del_col jc (id_mat m ! jc))"
  proof -
    have unit: "id_mat m ! jc = map (\<lambda>c. if jc = c then (1::int) else 0) [0..<m]"
      using j2 by (simp add: id_mat_def nth_map)
    have "del_col jc (map (\<lambda>c. if jc = c then (1::int) else 0) [0..<m]) = replicate (m - 1) 0"
      by (rule aux_el_delcol_unit) (rule j1, rule j2)
    hence "del_col jc (id_mat m ! jc) = replicate (m - 1) 0" using unit by simp
    thus ?thesis by (simp add: zrow_def)
  qed
  have mem: "del_col jc (id_mat m ! jc) \<in> set (map (del_col jc) (tl (id_mat m)))"
    using row_in by simp
  show ?thesis using tl_eq mem zr by (auto simp add: zhas_def)
qed

text \<open>--- K: the i = 0 branch, det (row_add_matrix m 0 jc f) = 1 ---\<close>
theorem aux_el_det_elementary_i0:
  assumes m0: "0 < m" and j1: "0 < jc" and j2: "jc < m"
  shows "det (row_add_matrix m 0 jc f) = (1::int)"
proof -
  let ?E = "row_add_matrix m 0 jc f"
  let ?r0 = "map (\<lambda>c. if c = jc then f else (if c = 0 then (1::int) else 0)) [0..<m]"
  have hd: "hd ?E = ?r0" by (rule aux_el_row0) (rule m0)
  have ne: "?E \<noteq> []"
  proof
    assume "?E = []"
    have lenE: "length ?E = m"
    proof -
      have "length (row_add_matrix m 0 jc f) = m"
        by (simp add: row_add_matrix_def)
      thus ?thesis .
    qed
    hence "m = 0" using \<open>?E = []\<close> by simp
    thus False using m0 by simp
  qed
  have E_eq: "?E = ?r0 # tl ?E"
  proof -
    have a: "hd ?E # tl ?E = ?E" by (rule hd_Cons_tl) (rule ne)
    show ?thesis using a hd by simp
  qed
  have lenr0: "length ?r0 = m" by simp
  have unfold: "det ?E
      = sum_list (map (\<lambda>k. (-1) ^ k * ?r0 ! k
          * det (map (del_col k) (tl ?E))) [0..<m])"
  proof -
    have "det ?E = det (?r0 # tl ?E)" using E_eq by simp
    also have "\<dots> = sum_list (map (\<lambda>k. (-1) ^ k * ?r0 ! k
          * det (map (del_col k) (tl ?E))) [0..<length ?r0])"
      by (simp add: det.simps(2))
    finally show ?thesis using lenr0 by simp
  qed
  let ?g = "\<lambda>k. (-1) ^ k * ?r0 ! k * det (map (del_col k) (tl ?E))"
  have gz: "\<And>k. 0 < (k::nat) \<Longrightarrow> k < m \<Longrightarrow> ?g k = (0::int)"
  proof -
    fix k :: nat
    assume k1: "0 < k" and k2: "k < m"
    show "?g k = (0::int)"
    proof (cases "k = jc")
      case True
      have z: "zhas (map (del_col jc) (tl ?E))"
        by (rule aux_el_tail_zhas) (rule j1, rule j2, rule m0)
      hence "det (map (del_col k) (tl ?E)) = (0::int)"
        using True by (simp add: aux_det_zero_row)
      thus ?thesis using True by simp
    next
      case False
      have "?r0 ! k = (0::int)" using k1 k2 False by (simp add: nth_map nth_upt)
      thus ?thesis using False by simp
    qed
  qed
  have collapse: "sum_list (map ?g [0..<m]) = ?g 0"
    by (rule aux_el_collapse_var) (rule m0, rule gz)
  have g0: "?g 0 = (1::int)"
  proof -
    have a: "?r0 ! 0 = (1::int)" using j1 m0 by (simp add: nth_map nth_upt)
    have b: "map (del_col 0) (tl ?E) = id_mat (m - 1)" by (rule aux_el_minor0) (rule m0)
    have c: "det (id_mat (m - 1)) = (1::int)" by (rule aux_det_id_mat)
    show ?thesis using a b c by simp
  qed
  show ?thesis using unfold collapse g0 by simp
qed

end
