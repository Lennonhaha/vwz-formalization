# `rank_outer_sum_le_two` 成本试算（2026-10-23）

> 只读试算报告。基线：`46117f1`（PR #15 squash 后）。本轮零改动、零 build。
> 目的：在动笔写 ②③④⑤ 之前，先量出「内维秩界」这条路线（路线 A）的真实成本，
> 并回答三个问题：④ 能否挂在现有 `zero_below` 归纳上、⑤ 是否需要 3×3 行列式、
> 若 ⑤ 超 300 行则「次可加性 + 文档化 TODO」的降级方案是否成立。

## 结论摘要

| 问题 | 结论 |
|---|---|
| ④ 能否挂 `zero_below` 归纳 | 能挂**同一条** `induct f`，但**必须改 `rref_fuel_shape` 的签名**（加 `staircase` 前提），不是「加一个合取项」 |
| ④ 成本 | **120–180 行**（原估 20–40 行，低了 4–6 倍） |
| ⑤ 是否需要 3×3 行列式 | **不需要也能做**，但两条路都贵：det3 反证路 **150–230 行**；独立性框架路 **300+ 行** |
| 降级方案（次可加性 + TODO） | **不成立**——它不解决 `≤ 2`，只是把 sorry 换个名字 |
| 路线 A 总量 | 原估 330–560 行 → **重估 740–1020 行**，命中红线 |

## 一、④ 能否挂在现有 `zero_below` 归纳上

### 判定：能挂同一条归纳，但必须改陈述的签名

`zero_below` 是纯**输出**性质（`aligned/VWZ_Rank.thy:1186`）。而阶梯性质在归纳里是**双向**的：

- 递归调用需要**输入前提**：`rows 0..r-1` 已是阶梯，且 `lead < c`；
- 输出需要给**结论**：`rows 0..r0-1` 是阶梯，且 `lead < c0`。

因此 `rref_fuel_shape` 要从

```
zero_below r c A ⟹ r ≤ c ⟹ c ≤ n_cols A ⟹ is_rect A ⟹ ∃r0 c0. …
```

改成

```
staircase r c A ⟹ zero_below r c A ⟹ … ⟹ ∃r0 c0. … ∧ staircase r0 c0 (rref_fuel f r c A)
```

即**改签名**，不是加合取项。代价是所有调用点（`mat_rank_le_n_cols`、将来的 ②③）都要补这个前提。

### 已有基础（省下 60–80 行）

`lead` 机器已存在，带 seg marker `rank-lead-invmod-20261023`：

| 组件 | 位置 |
|---|---|
| `fun lead :: int list ⇒ nat` | `VWZ_Rank.thy:779` |
| `lead_le_length` | L783 |
| `lead_nth_zero` | L786 |
| `lead_nth_nonzero` | L815 |
| `lead_eq_length_all_zero` | L837 |

### 新坑（直接影响估算）

`eliminate_col` **不是只消下方**：

```
eliminate_col A r c = foldl (λB k. if k = r then B else add_row_mult B k r (- entry B k c)) A [0..<n_rows A]
```

（`aligned/VWZ_RREF.thy:274`）

它遍历 `0..n_rows-1` 中除 `r` 以外的**全部**行，`k < r` 的行也被 `add_row_mult` 改动。因此「前缀阶梯不受扰动」**不能**用「行未动」证明，只能证「**列 < c 的项未变**」（row r 在 `c` 左边全零，加它的倍数不改左边）—— 这是一条 fold 归纳引理，约 35–45 行。

### 成本分项

| 项 | 行数 |
|---|---|
| `staircase` 定义 | 5 |
| pivot 步 `lead (row r) = c`（用现成 `entry_scale_row_pivot` / `pivot_some_zeros` / `entry_eliminate_col_self`） | 40–55 |
| 前缀 `lead` 保持（上面的 fold 引理） | 35–45 |
| 三分支维护 | 30–45 |
| 调用点补前提 | 20–40 |
| **合计** | **130–190**（取中 **120–180**） |

**折扣**：② 需要的是**同一条**「列 < c 不变」引理，②④ 可共享，合计减 30–40 行。

## 二、⑤ 是否需要 3×3 系数行列式

### 判定：不需要行列式也能做，但两条路都不便宜

现有材料（实测）：

| 材料 | 位置 | 状态 |
|---|---|---|
| `det3`（整数 3×3，六项展开） | `VWZ_Matrix.thy:200` | 有 |
| `det2` / `minor2` 恒等式群（swap / scale / add / repeat，12 条） | `VWZ_ModAlgebra.thy:2689–3060` | 有，但**只到 2×2** |
| `rank ≤ 1 ⟹ 2×2 minors 消失` | `VWZ_Rank.thy`（`rank_le_one_imp_minors_vanish`） | 有单向 |
| `prime (3329::int)` | `VWZ_Aux.thy:31`（`aux_prime_int'`） | 有 |
| `invmod` + `invmod_correct` | `VWZ_Rank.thy:880 / 1018` | 有 |
| `det3` 行多线性 | — | **没有** |
| `det3` 重复行 = 0 | — | **没有** |
| 线性组合 / 线性独立 词汇 | — | **完全没有** |

### 两条路

**(a) 独立性框架**：先造「行组合 = ∑ cᵢrᵢ」「独立集」谓词，再证阶梯行独立，再证 `span{p,q}` 内独立集 ≤ 2。
**300+ 行**，且前一半是与被证命题无关的纯脚手架。

**(b) det3 反证框架（推荐评估）**：设 `rref M` 有 ≥ 3 非零行、`lead` 严格递增 `l1<l2<l3`。取 `(l1,l2,l3)` 三列的 3×3 限制 `U`：

1. 阶梯 ⇒ `U` 上三角、对角非零 mod q ⇒ `det3 U mod 3329 ≠ 0`；
2. 每行 = `aᵢ·p + bᵢ·q` ⇒ `det3 U` 展开成 8 项，每项两行同源 ⇒ `≡ 0`；
3. 矛盾 ⇒ 秩 ≤ 2。

这条路**完全绕开独立性词汇**，只需 det3 的多线性、重复行为零、三角非零、以及「逐项同余 ⇒ det3 同余」四条。

**关键洞察**：第 2 步不需要在 `fq` 层做多项式化简。整数层 `det3` 的三行若是 `aᵢ·p + bᵢ·q`，多线性展开后每项有两个相同行，**作为整数恒等式即为 0**；`fq` 包裹只影响同余，用一条「逐项同余 ⇒ det3 同余」把整数 0 搬到 mod q 层即可。

**fq/mod 桥接成本**：约 30–40 行（一条 `det3_cong`），不需要额外的域论。

### 成本

| 组成 | 行数 |
|---|---|
| 多线性（行缩放 + 行相加） | 15–25 |
| 重复行为零（3 个位置） | 15–25 |
| 上三角 + 乘积非零 mod q | 25–40 |
| `det3_cong`（逐项同余） | 30–45 |
| 三行落在 span 内 ⇒ det3 ≡ 0（8 项展开） | 40–70 |
| 接入 `rref`（3 个 lead + 三角化 + 反证） | 30–50 |
| **合计** | **155–255**（取中 **150–230**） |

## 三、降级方案是否真能推 `rank_outer_sum_le_two`

### 判定：不成立，它只是把 sorry 换个名字

三条硬证据：

1. **同一个 `≤ 2`**。`T2_B7`（`aligned/VWZ_ObligationsAligned.thy:790–800`）要的是 `mat_rank (psi_slice pk i) = 2`。`≥ 2` 方向已由 `rank_ge_two_of_nonzero_minor` 解决（文件 L764–772 明说），**唯一缺口就是 `≤ 2`**。次可加性恰好卡在同一个 `≤ 2` 上。
2. **次可加性不是更便宜的近似**。`rank(A+B) ≤ rank(A) + rank(B)` 要么调用**同一个**「rank ≤ 生成集大小」（内维秩界本身），要么走行空间维数理论（比 ④⑤ 更贵）。
3. **`outer_sum2` 不是矩阵加法定义的**。`aligned/VWZ_Rank.thy:27–34` 明确写「not spelled as a matrix addition because no such operation is needed anywhere else」。走次可加性还要先补 `mat_add` + `outer_sum2 = mat_add (outer u v) (outer u' v')`（约 50–70 行），再加次可加性本体。

**唯一诚实的降级**：保留 `T2_B7` 的 sorry，但把缺失引理**取名字、定位置**：

```
mat_rank_le_two_of_rows_in_span:
  length p = length q ⟹ rows_in_span p q M ⟹ mat_rank M ≤ 2
```

### 写法约束（`count-obligations.cjs` 口径实测）

- **账本**只数 `aligned/VWZ_ObligationsAligned.thy` 内按 `section` 分层的 `lemma` 与 `sorry` → 当前 58 / 7。
- **`sorry` 门禁**扫描**全仓** `.thy`（含 `_tmp/`、`neg/`、`smoke/`、`skeleton/`、`paper/`），任何行首为 `sorry` 的证明步骤只要不在账本文件里就 **FAIL（exit 1）**。
- 因此：**注释里的陈述不影响账本**；写成 `lemma … sorry` 会立刻把门禁打红（不是「+1」而是整体 FAIL）。

## 四、路线 A 总量重估

用 ① 的实测系数（213 行 vs 原估 80–120，约 1.9×）与 ④⑤ 的新认识：

| 步骤 | 原估 | 重估 | 依据 |
|---|---|---|---|
| ① | 80–120 | **213（实际）** | 显式证明结构 + 边界转换 |
| ② | 40–70 | 80–130 | 与 ④ 共享「列 < c 不变」引理 |
| ③ | 60–100 | 120–200 | 燃料归纳三分支 + 不变量双向 |
| ④ | 20–40 | **120–180** | 需改签名 + `eliminate_col` 全行性 |
| ⑤ | 100–180 | **150–230**（det3 路）/ 300+（独立集路） | 需新建 det3 多线性 |
| ⑥ | 30–50 | 40–70 | — |
| **合计** | 330–560 | **740–1020** | 命中 550–800 上限之外 |

## 五、下一步闸门

不做整条路线 A，改为**分阶段测量闸门**：

1. **⑤ 的 det3 极小试点**（`_tmp/det3-probe.thy`，独立 session，不碰 `aligned/`，不含 `sorry`）：
   只测 ⑤ 需要的四条代数事实。
2. **判据**：四条合计 **≤ 120 行** ⇒ det3 路成立，⑤ 可压到 150–200，路线 A 总量约 720（偏贵但可控）；
   **> 120 行** ⇒ ⑤ 必然 300+，**立即停**，转「文档化 + 保留 sorry」，预算挪到其余 6 个 sorry。
3. 若停：把 `mat_rank_le_two_of_rows_in_span` 的陈述 + `TODO(proof)` 写进 `VWZ_Rank.thy` **注释**（不是 `lemma`），账本保持 58 / 7，`sorry` 门禁保持绿。

## 附：本轮未改动

- `aligned/` 零改动；`T2_B7` 的 sorry 未动；`exact-step-ee44bc6` 备份分支未动；未 build 主会话。

## 六、det3 极小试点结果（2026-10-23 同日晚）

试点文件：`_tmp/Det3Base.thy`、`_tmp/Det3Span2.thy`、`_tmp/ROOT`（独立 session
`Det3Base`，parent = `HOL-Number_Theory`，`options [quick_and_dirty = false]`，无 `sorry`）。
`det3` / `entry` 为对齐层定义的副本，避免依赖 `VWZ_A3_Aligned` 的堆。

### 闸门引理：81 行（≤ 120，判据通过）

| 族 | 条数 | 行数 | 证明方式 |
|---|---|---|---|
| 行多线性（scale ×3、add ×3） | 6 | 33 | `by (simp add: det3_def entry_def algebra_simps)` |
| 重复行为零（01 / 02 / 12） | 3 | 12 | 同上 |
| 上三角求值 + 乘积非零 mod q（含素性辅助 2 条） | 2 | 36 | 同上 + `prime_dvd_mult_iff` |
| **合计** | **11** | **81** | — |

### 决定性引理：自动方法不通

`det3_span2`（三行各为 `aᵢ·p + bᵢ·q` ⇒ `det3 = 0`，12 变量 6 次齐次）：

| 尝试 | 结果 |
|---|---|
| `by (simp add: det3_def entry_def algebra_simps)` | 化简后残留多项式等式，未闭合 |
| `by (simp add: ... ac_simps)` | 发散，被 `timeout` 中断（`Interrupt_Breakdown`） |
| `unfolding det3_def entry_def by algebra` | 未闭合 |
| `by (simp add: det3_def entry_def; algebra)` | 未闭合 |

结论：这条恒等式**无法用现成的 simp/algebra 自动化闭合**，必须结构化展开（把三行分别按
`a·p + b·q` 拆成 8 项、每项用重复行为零消掉）。按 ② 的实测系数（显式结构 ≈ 1.5–2× 乐观估计），
这条引理预计 **40–70 行**。

### 由此更新的判断

- 闸门字面判据（三条 ≤ 120 行）**通过：81 行**；
- 但闸门想去的风险（⑤ 能否压到 150–200）**未被完全去风险**：
  `det3_span2` 是 ⑤ 的核心，自动化不通意味着它的成本只能靠结构化证明估，
  ⑤ 现实区间变为 **190–270**（原估 150–230），路线 A 总量 **780–1080**。
- 另一个实测副作用：`prime (3329::int)` 与字面量 `3329` 的类型规范化需要一条
  `of_nat_numeral [symmetric]` 的转换（`prime (int 3329)` 与 `3329 dvd …` 不能靠 metis 直接合一），
  这条坑记 5–10 行。

### 下一个微闸门

`det3_span2` 的结构化证明，**限定 ≤ 70 行**：

- 成功且 ≤ 70 行 ⇒ det3 路成立，⑤ ≈ 200–240，可进入 ②（并把 ④ 与 ② 共享的「列 < c 不变」引理一并做）；
- > 70 行或写不出 ⇒ 停止路线 A，转「注释里命名 `mat_rank_le_two_of_rows_in_span` + 保留 sorry」，
  账本保持 58 / 7（`count-obligations.cjs` 实测：`lemma … sorry` 写在账本外会让门禁 **exit 1**，
  注释则不影响）。

### 本轮未改动（复核）

- `aligned/` 零改动；`T2_B7` 的 sorry 未动；`exact-step-ee44bc6` 未动；
- `node tools/count-obligations.cjs` 仍 **7 sorry，outside 0，OK**（试点文件不含 sorry）；
- 新增仅 `docs/vwz/rank-outer-sum-cost-20261023.md` 与 `_tmp/{ROOT,Det3Base.thy,Det3Span2.thy,det3-b*.log}`。

## 七、微闸门结果：`det3_span2` 通过（9 行）

判决：**通过，且远低于 70 行上限**。构建 `isabelle build -b -j 2 -d _tmp Det3Base` **rc=0，18 s**。

### 关键突破：不必手写 8 项

前一轮的失败不是「恒等式太贵」，而是**收尾方式错了**。实测发现两件事：

1. 用 `simp only: <6 条多线性引理>` 展开后，左边得到的是**嵌套形式**
   `a3 * (a2 * (a1 * X1 + b1 * X5) + b2 * (a1 * X3 + b1 * X7)) + …`，
   右边是我手写的**扁平 8 项** —— 两者只差乘法结合律，结构完全正确。
   所以「展开」本身是便宜的，贵的是**把嵌套形式重排成扁平形式**（那才需要 12 变量多项式归一）。

2. 正确的收尾是让**重复行引理直接把每一项打成 0**，再让一个普通 `simp` 只做地面算术
   （`x * 0 = 0`、`0 + 0 = 0`）：

```
by (simp only: det3_add_row0 det3_add_row1 det3_add_row2
               det3_scale_row0 det3_scale_row1 det3_scale_row2
               det3_repeat_01 det3_repeat_02 det3_repeat_12;
    simp)
```

这样既不做重排、也不做多项式归一，**9 行闭合**（陈述 6 行 + 证明 3 行）。
前一轮「40–70 行」的估计是**按手写 8 项算的，方向错了**。

### 另一个实测坑：`of_nat_numeral [symmetric]` 会发散

`by (simp only: of_nat_numeral [symmetric])` 用在 `prime (int 3329) ⇒ prime (3329::int)`
上会与默认的 `of_nat_numeral` 形成重写环，触发 `Interrupt_Breakdown`（实测两次）。
正解：显式给等式 `(int 3329) = (3329::int)` 再 `by metis`。

### 成本重估（第三次，向下修正）

| 项 | 二次估计 | 本次实测/修正 |
|---|---|---|
| det3 代数基础（多线性/重复行/三角） | 81 | **82**（含素性辅助，实测） |
| 决定性引理 `det3_span2` | 40–70 | **9** |
| ⑤ 合计（含 `fq`/`map2` 真实形态的管道 + `det3_cong` + 接入 rref） | 190–270 | **150–220** |

⑤ 回到初始区间（150–230）的下半段。路线 A 总量：**740–980**（仍高于最初 330–560，
但低于二次估计的 780–1080）。

### 仍未验证的部分（⑤ 的真实形态）

试点用的是**字面量矩阵**（`[[a1*p1 + b1*q1, …], …]`），真实 ⑤ 需要：

- 行是 `map2` 生成的（`psi_slice_of` 的形状），带 `length` 前提；
- 元素带 `fq` 包裹（`… mod 3329`），需要 `det3_cong`（逐项同余 ⇒ det3 同余）;
- 三行的组合系数依赖行下标（`ua ! i`、`ub ! i`），不能当常数。

这三项是**下一段（②）的真实成本**，不是本闸门能覆盖的。本闸门只回答了「det3 恒等式本身贵不贵」——
答案是**不贵**。

### 结论

det3 路**成立**，不再需要「停止路线 A」。下一步按原计划：②（`rref` 行仍在 span 内）+ ④ 共享的
「列 < c 不变」引理，两者合起来做一次测量闸门。
