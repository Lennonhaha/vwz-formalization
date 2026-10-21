(*  Title:      VWZ_Target.thy
    SPDX-License-Identifier: Apache-2.0

    Bookkeeping for the sparse target: the walk preserves the pool's length, set
    and distinctness, so its first k+1 entries are k+1 distinct positions inside
    the range; and the indicator of such a support has Hamming weight equal to
    the support's length.

    Kept in its own theory because none of it is about the protocol.  It is the
    loop invariant of the selection, and it is proved here so that a failed
    attempt cannot leave the obligation file half-rewritten.
*)

theory VWZ_Target
  imports VWZ_Fq3329
begin

text \<open>Hamming weight: the number of non-zero entries.  This used to live in the
  obligation file; it is needed here first, so it moved.\<close>

definition weight :: "nat list \<Rightarrow> nat" where
  "weight xs = length (filter (\<lambda>x. x \<noteq> 0) xs)"

section \<open>Swapping one pair of positions\<close>

lemma length_swap_at [simp]:
  "length (swap_at i j xs) = length xs"
  by (simp add: swap_at_def)

lemma set_swap_at:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> set (swap_at i j xs) = set xs"
  by (simp add: swap_at_def)

lemma distinct_swap_at:
  "distinct xs \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
     distinct (swap_at i j xs)"
  by (simp add: swap_at_def)

section \<open>The walk preserves the pool\<close>

text \<open>All three invariants are now one rewrite away, because swapping preserves
  length, set and distinctness and no step touches the pool's length.\<close>

lemma fy_fuel_len:
  "\<And>j xs rs. length (fy_fuel f j xs rs) = length xs"
proof (induct f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show "length (fy_fuel (Suc f) j xs rs) = length xs"
  proof (cases rs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons r rs')
    have step: "fy_fuel (Suc f) j xs rs =
        (if j < length xs
         then fy_fuel f (Suc j) (swap_at j (j + r mod (length xs - j)) xs) rs'
         else xs)"
      using Cons by simp
    show ?thesis
    proof (cases "j < length xs")
      case True
      have "length (fy_fuel f (Suc j) (swap_at j (j + r mod (length xs - j)) xs) rs')
          = length (swap_at j (j + r mod (length xs - j)) xs)"
        using Suc.hyps by simp
      with step True show ?thesis by simp
    next
      case False
      with step show ?thesis by simp
    qed
  qed
qed

lemma fy_fuel_set:
  "\<And>j xs rs. set (fy_fuel f j xs rs) = set xs"
proof (induct f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  show "set (fy_fuel (Suc f) j xs rs) = set xs"
  proof (cases rs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons r rs')
    have step: "fy_fuel (Suc f) j xs rs =
        (if j < length xs
         then fy_fuel f (Suc j) (swap_at j (j + r mod (length xs - j)) xs) rs'
         else xs)"
      using Cons by simp
    show ?thesis
    proof (cases "j < length xs")
      case False
      with step show ?thesis by simp
    next
      case True
      let ?i = "j + r mod (length xs - j)"
      have hj: "0 < length xs - j" using True by simp
      have mr: "r mod (length xs - j) < length xs - j" by (rule mod_less_divisor[OF hj])
      have ib: "?i < length xs"
      proof -
        have "j + r mod (length xs - j) < j + (length xs - j)" using mr by simp
        also have "j + (length xs - j) = length xs" using True by simp
        finally show ?thesis .
      qed
      have st: "set (swap_at j ?i xs) = set xs"
        by (rule set_swap_at) (simp_all add: True ib)
      have "set (fy_fuel f (Suc j) (swap_at j ?i xs) rs') = set (swap_at j ?i xs)"
        using Suc.hyps by simp
      with step st True show ?thesis by simp
    qed
  qed
qed

lemma fy_fuel_distinct:
  "\<And>xs j rs. distinct xs \<Longrightarrow> distinct (fy_fuel f j xs rs)"
proof (induct f)
  case 0
  then show ?case by simp
next
  case (Suc f)
  fix xs :: "nat list" and j :: nat and rs :: "nat list"
  assume d: "distinct xs"
  show "distinct (fy_fuel (Suc f) j xs rs)"
  proof (cases rs)
    case Nil
    then show ?thesis using d by simp
  next
    case (Cons r rs')
    have step: "fy_fuel (Suc f) j xs rs =
        (if j < length xs
         then fy_fuel f (Suc j) (swap_at j (j + r mod (length xs - j)) xs) rs'
         else xs)"
      using Cons by simp
    show ?thesis
    proof (cases "j < length xs")
      case False
      with step d show ?thesis by simp
    next
      case True
      let ?i = "j + r mod (length xs - j)"
      have hj: "0 < length xs - j" using True by simp
      have mr: "r mod (length xs - j) < length xs - j" by (rule mod_less_divisor[OF hj])
      have ib: "?i < length xs"
      proof -
        have "j + r mod (length xs - j) < j + (length xs - j)" using mr by simp
        also have "j + (length xs - j) = length xs" using True by simp
        finally show ?thesis .
      qed
      have ds: "distinct (swap_at j ?i xs)"
        by (rule distinct_swap_at) (simp_all add: d True ib)
      have ih: "distinct (fy_fuel f (Suc j) (swap_at j ?i xs) rs')"
        using Suc.hyps ds by simp
      with step True show ?thesis by simp
    qed
  qed
qed

section \<open>The support\<close>

lemma support_len:
  "length (take (k + 1) (fy_fuel (k + 1) 0 [0..<par_n k] (digest k msg))) = k + 1"
proof -
  have l: "length (fy_fuel (k + 1) 0 [0..<par_n k] (digest k msg)) = par_n k"
    by (simp add: fy_fuel_len)
  have le: "k + 1 \<le> par_n k" by (simp add: par_n_def)
  have "length (take (k + 1) (fy_fuel (k + 1) 0 [0..<par_n k] (digest k msg)))
      = min (k + 1) (par_n k)" using l by (simp add: length_take)
  also have "\<dots> = k + 1" using le by (simp add: min_absorb2)
  finally show ?thesis .
qed

lemma support_distinct:
  "distinct (take (k + 1) (fy_fuel (k + 1) 0 [0..<par_n k] (digest k msg)))"
  by (simp add: fy_fuel_distinct)

lemma support_subset:
  "set (take (k + 1) (fy_fuel (k + 1) 0 [0..<par_n k] (digest k msg)))
     \<subseteq> {0..<par_n k}"
  by (auto dest: in_set_takeD simp: fy_fuel_set)

section \<open>Counting the indicator\<close>

text \<open>The support has no repeats and sits inside the range, so the indicator is
  one exactly on the support.  The induction splits on whether the last position
  belongs to the support; in the positive branch the support shrinks by exactly
  one element via @{text remove1}.\<close>

lemma weight_indicator:
  "\<And>S. distinct S \<Longrightarrow> set S \<subseteq> {0..<n} \<Longrightarrow>
     weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]) = length S"
proof (induct n)
  case 0
  fix S :: "nat list"
  assume d: "distinct S" and sub: "set S \<subseteq> {0..<0}"
  have "set S = {}" using sub by simp
  then have "S = []" by auto
  then show "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<0]) = length S"
    by (simp add: weight_def)
next
  case (Suc n)
  fix S :: "nat list"
  assume d: "distinct S" and sub: "set S \<subseteq> {0..<Suc n}"
  have upt: "[0..<Suc n] = [0..<n] @ [n]" by simp
  show "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<Suc n]) = length S"
  proof (cases "n \<in> set S")
    case True
    define S' where "S' = remove1 n S"
    have dS': "distinct S'" using d \<open>n \<in> set S\<close> by (simp add: S'_def)
    have sub': "set S' \<subseteq> {0..<n}"
      using sub d \<open>n \<in> set S\<close> by (auto simp: S'_def)
    have ih: "weight (map (\<lambda>j. if j \<in> set S' then 1 else 0) [0..<n]) = length S'"
      using Suc.hyps dS' sub' by simp
    have last: "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<Suc n])
        = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]) + 1"
    proof -
      have wapp: "\<And>xs ys. weight (xs @ ys) = weight xs + weight ys"
        by (simp add: weight_def)
      have "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<Suc n])
          = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) ([0..<n] @ [n]))"
        by (simp add: upt)
      also have "\<dots> = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]
                        @ [(if n \<in> set S then 1 else 0)])"
        by simp
      also have "\<dots> = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n])
                        + weight [(if n \<in> set S then 1 else 0)]"
        by (simp add: wapp)
      also have "\<dots> = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]) + 1"
        using \<open>n \<in> set S\<close> by (simp add: weight_def)
      finally show ?thesis .
    qed
    have se: "set S' = set S - {n}" using d by (simp add: S'_def)
    have me: "map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]
        = map (\<lambda>j. if j \<in> set S' then 1 else 0) [0..<n]"
    proof (rule map_cong[OF refl])
      fix j
      assume "j \<in> set [0..<n]"
      then have jn: "j < n" by simp
      have jne: "j \<noteq> n" using jn by auto
      show "(if j \<in> set S then 1 else 0) = (if j \<in> set S' then 1 else 0)"
      proof (cases "j \<in> set S")
        case True
        have "j \<in> set S'" using se \<open>j \<in> set S\<close> jne by auto
        with True show ?thesis by simp
      next
        case False
        have "j \<notin> set S'" using se \<open>j \<notin> set S\<close> by auto
        with False show ?thesis by simp
      qed
    qed
    have same: "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n])
        = weight (map (\<lambda>j. if j \<in> set S' then 1 else 0) [0..<n])"
      by (subst me, rule refl)
    have lenS: "length S = Suc (length S')"
    proof -
      have ne: "S \<noteq> []" using \<open>n \<in> set S\<close> by auto
      have "length S' = length S - 1" using \<open>n \<in> set S\<close> by (simp add: S'_def length_remove1)
      with ne show ?thesis by simp
    qed
    have "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<Suc n])
        = weight (map (\<lambda>j. if j \<in> set S' then 1 else 0) [0..<n]) + 1"
      using last same by simp
    also have "\<dots> = length S' + 1" using ih by simp
    also have "\<dots> = length S" using lenS by simp
    finally show ?thesis .
  next
    case False
    have sub': "set S \<subseteq> {0..<n}"
    proof
      fix x
      assume xS: "x \<in> set S"
      with sub have xs: "x < Suc n" by auto
      have xn: "x \<noteq> n" using xS \<open>n \<notin> set S\<close> by auto
      with xs show "x \<in> {0..<n}" by simp
    qed
    have ih: "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]) = length S"
      using Suc.hyps d sub' by simp
    have "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<Suc n])
        = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n])"
    proof -
      have wapp: "\<And>xs ys. weight (xs @ ys) = weight xs + weight ys"
        by (simp add: weight_def)
      have "weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<Suc n])
          = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) ([0..<n] @ [n]))"
        by (simp add: upt)
      also have "\<dots> = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]
                        @ [(if n \<in> set S then 1 else 0)])"
        by simp
      also have "\<dots> = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n])
                        + weight [(if n \<in> set S then 1 else 0)]"
        by (simp add: wapp)
      also have "\<dots> = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<n]) + 0"
        using \<open>n \<notin> set S\<close> by (simp add: weight_def)
      finally show ?thesis by simp
    qed
    with ih show ?thesis by simp
  qed
qed

section \<open>The target lemma\<close>

lemma hash_target_weight:
  "weight (hash_target k msg) = k + 1"
proof -
  define S where "S = take (k + 1) (fy_fuel (k + 1) 0 [0..<par_n k] (digest k msg))"
  have lenS: "length S = k + 1"
    using support_len unfolding S_def by simp
  have dS: "distinct S"
    using support_distinct unfolding S_def by simp
  have subS: "set S \<subseteq> {0..<par_n k}"
    using support_subset unfolding S_def by simp
  have "weight (hash_target k msg)
      = weight (map (\<lambda>j. if j \<in> set S then 1 else 0) [0..<par_n k])"
    unfolding hash_target_def S_def by simp
  also have "\<dots> = length S" using weight_indicator dS subS by simp
  also have "\<dots> = k + 1" using lenS by simp
  finally show ?thesis .
qed

end
