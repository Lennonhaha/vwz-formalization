# VWZ A3 对齐版骨架 —— 首份真正跑通的 Isabelle 骨架

> 2026-10-18 · 授权级 L1（本地可回滚）· 会话 workspace `plans/vwz-a3-isabelle/aligned/`

## 一句话结论

`isabelle build -D aligned` → **RC = 0**（`Finished VWZ_A3_Aligned (0:00:03)`）。
T0 的 8 条义务（17 个引理）**零 `sorry`**；T1 14 条、T2 8 条、T3 8 条保留 `sorry` + `TODO(define)`。

> **最新状态（2026-10-19 00:5x，见文末 Addendum）**：`A4/A5/A6/A7` 均已闭环（`A7` 本轮拿下）。
> 当前计数 **T0 17/0 ｜ T1 21/5 ｜ T2 8/8 ｜ T3 8/8 = 54 引理 / 21 sorry（raw 23）**，`ALIGNED_RC=0`。
> T1 剩余 5 条（`B4 C2 C6 F1_pk F1_sig`）均阻塞于未定义常量，非证明技术问题。

## 交付物

| 文件 | 内容 |
|---|---|
| `aligned/ROOT` | `session VWZ_A3_Aligned = "HOL-Number_Theory" +`（`options [quick_and_dirty]`） |
| `aligned/VWZ_Fq3329.thy` | 定义层：域的锚定 + 参数 + 序列化原语 + 协议对象（`consts`+TODO） |
| `aligned/VWZ_ObligationsAligned.thy` | 37 条义务，按 T0–T3 分层 |
| `ROOTS` | 增列 `aligned`（原 `smoke / neg / skeleton` 保留） |

## 定义层（residue_ring 路线）

- `lemma prime_3329: "prime (3329::nat)" by eval`
- `interpretation Fq3329: residues_prime 3329 "residue_ring (int 3329)" by unfold_locales (rule prime_3329)`
- `abbreviation Fq ≡ residue_ring (int 3329)`
- 事实：`Fq_carrier`（`carrier Fq = {0..3328}`）、`Fq_card`（`= 3329`）、`Fq_is_field`、`Fq_add_eq`、`Fq_mult_eq`、`Fq_zero_eq`、`Fq_one_eq`
- 编码：`le1`、`u16le`、`ser_pk`、`ser_sig` 及长度引理（`u16le_concat_len`、`ser_pk_len`、`ser_sig_len`）
- 协议对象：`KeyGen / hash_target / Eval / Sign / Verify / SeedRng / distinct_lam / sample_below / nullspace / solve_linear`，全部 `consts` + `TODO(define)`

## 控制项证据（四控 + 附证）

| 控制 | 会话 | 结果 |
|---|---|---|
| 正控 解释成立 + 定义层可证 | `_probe2` / `_diag` | ✅ `DIAG_RC=0`（3s） |
| 负控 `prime (6::nat)` | `_negprobe` | ✅ FAIL（定位到 line 6） |
| 附证 `field (ZMod 3329)` | `_zmodprobe` | ✅ FAIL —— 故 **不用裸 `ZMod`，改走 `residue_ring`** |
| 定义层 `simp add: residue_ring_def` | `_diag` | ✅ 五个 `*_via_def` 引理全过 |

### 踩到的真实坑（已固化）

1. **`prime n by simp` 会挂死**（≥20 分钟 CPU 不收敛）→ 一律改 `by eval`（`_probe` 首轮的元凶）。
2. **裸 `res_carrier_eq` 未定义**，须带 `Fq3329.` 前缀；且 sublocale 导出的 residue 事实（`res_carrier_eq`/`res_add_eq`/`res_prime_units_eq`）**不能直接 `simp add:`** —— 改用 `simp add: residue_ring_def` 展开定义（`Fq3329.is_field` 例外，`rule` 可用）。
3. **`consts` 不能多名字**：`consts A B :: t` 语法错误 → 必须逐个声明。
4. **文档注记**：`subsection \<open>... m\<^sup>2 ...\<close>` 报 `Undefined document antiquotation: sup` → 用 `m^2`。
5. **分布律名**：`left_distrib` 不存在 → 用 `distrib_left` / `distrib_right`。
6. **环操作乘法律**：`simp add: residue_ring_def mod_mult_right_eq mod_mult_left_eq mod_add_right_eq mod_add_left_eq ac_simps`。

## T0 明细（8 条 / 17 引理 / **0 sorry**）

| 义务 | 引理 | 手法 |
|---|---|---|
| B6 | `T0_B6`（KeyGen 纯度） | `by simp` |
| B8 | `T0_B8`（`len ser_pk = 1+2·n·m²`） | `by simp`（长度引理 `[simp]`） |
| C4 | `T0_C4_size` / `T0_C4_ge3` | `by arith` |
| C5 | `T0_C5`（hash_target 纯度） | `by simp` |
| D2 | `atMost_Un_atLeast_nat` / `ZaZb_union` / `ZaZb_inter` / `T0_D2_card` | `card_Un_Int` + 割点集合模型 |
| D3 | `T0_D3`（u2 行数 = 2k+1） | `by arith` |
| D7 | `T0_D7`（Sign 纯度） | `by simp` |
| E3a | `accepts_len` + `T0_E3a_control_accept` + `N1..N5` | `by eval` |

> D2 建模说明：以「割点 c ∈ Z」模型化 §6.4 的前缀/后缀划分（`Za = Z ∩ {..c}`、`Zb = Z ∩ {c..}`），
> 得 `Za ∩ Zb = {c}`（恰 1 个共享下标）与 `|Za| + |Zb| = |Z| + 1`（`card_Un_Int`）。

## T1 已闭环（7 引理，`by simp add: residue_ring_def …`）

`A1`（加/乘交换）、`A2`（加/乘结合）、`A3`（分配律）、`F2`（sig 长度 `1+4m`）、`F3`（u16 小端定义）。

## T1 剩余 / T2 / T3（`sorry` + `TODO(define)`）

- T1 剩 14：`A4`(2) `A5`(2) `A6`(2) `A7`(2) `A8` `B4` `C2` `C6` `F1`(2)
- T2 全 8：`B2 B3 B5 B7 D4 D5 D6 D1`（矩阵/秩主体未定义）
- T3 全 8：`B1 C1 C3 D8 E1 E2 E3b E4`
- **明确不计为可证义务**：`T3_D8_empirical`（v0 标经验性，可能为假）、`T3_E3b_conjectural`（v0 §10.1 声明不可证）。

## 口径（不许糊数字）

- 总数 **37 = T0 8 + T1 13 + T2 8 + T3 8**（以 v0 formalization-plan 表为准）。
- **F2 口径说明**：v0 列 F1/F2/F3，但 tier 清单只列 F1/F3。本文件把 **F2（签名长度 `1+4m`）补入 T1 并注明**；pk 侧长度在 **T0-B8**。tier 清单的这处出入如实记录，不玩数字游戏。

## 环境记录

- Isabelle2025-2 位于 `D:\FIBEMATE\_tools\Isabelle2025-2`；无 `.bat`，经自带 cygwin `bash.exe --login` 调用，路径 `/cygdrive/...`。
- 依赖须 `"HOL-Number_Theory"`（仅 `HOL` 不够）。
- 同一 bash 会话内首次 `isabelle build` 慢（堆加载/首建），其后单会话 ~3–11s。
- 探针/诊断会话（`_probe` `_probe2` `_diag` `_negprobe` `_zmodprobe`）保留为控制项证据，未入 `ROOTS`。

---

## Addendum 18:55 -- A6 closed by type-pinning; T2 definition layer landed

- A6 root cause: the exponent of the overloaded `[^]` was left unconstrained, so
  the `nat_pow_*` monoid facts never matched the goal.  Fix: pin `::nat` on the
  exponent.  Proofs: `rule Fq3329.nat_pow_mult [symmetric], simp` and
  `rule Fq3329.nat_pow_pow, simp`.
- A7_inv_fermat exponent likewise pinned (`3329 - (2::nat)`); still sorry (fermat).
  *(superseded by Addendum 2026-10-19: A7 is now closed; this line is kept as history.)*
- VWZ_Matrix.thy 3923 -> 5440 bytes: real definitions for invmod, mat_rank1,
  mat_rank2, mat_slice2, mat_solve2, mat_nullspace (a vec SET), mat_inner;
  mat_rank / mat_solve remain TODO(define), pending RREF machinery.
- isabelle build -D aligned: RC=0.  Counts: T0 17/0 | T1 21/9 | T2 8/8 | T3 8/8;
  total 54 lemmas / 25 sorry (raw token 27).

---

## Addendum 2026-10-19 00:5x -- A7 closed (Fermat inverse + involution); T1 sorry 7 -> 5

- `T1_A7_inv_fermat` and `T1_A7_inv_inv` are now proven (no `sorry`).
  Probe evidence: `_a7probe/A7J.thy` RC=0 (Fermat), `_a7probe/A7IF.thy` RC=0 (involution).
- Route (group order over the units; **no** `fermat_theorem` bridge needed):
    1. `Units Fq = carrier Fq - {0}`   by `rule Fq3329.field_Units` (kept as a local fact)
    2. `x ∈ Units Fq`                   `using units cx nz by auto`
    3. `finite (Units Fq)`             by `rule Fq3329.finite_Units`
    4. `x [^] card (Units Fq) = 1`      `using finU xu by (rule Fq3329.units_power_order_eq_one)`
    5. `card (Units Fq) = 3328`         `using Fq3329.res_prime_units_eq by (subst Fq3329.res_prime_units_eq) simp`
    6. `Suc (3329-2) = card (Units Fq)` `using cardU by simp`
    7. h1/h2: `x[^](3329-2)⊗x = 1` and `x⊗x[^](3329-2) = 1` via
       `nat_pow_Suc` / `nat_pow_Suc2` (symmetric) + `subst e`, then `pow1`
    8. `show ?thesis using cx ycl h2 by (rule Fq3329.comm_inv_char)`
  Involution: `show ?thesis using xu by (rule Fq3329.Units_inv_inv)`.
- Mechanism notes (probe-verified this round):
    * interpretation/locale-exported facts do **not** rewrite under `simp add:`
      (`field_Units` and `res_prime_units_eq` both confirmed non-firing), **but**
      `subst <fact>` and `using <fact> by simp` **do** fire, and `rule <fact>` applies.
      ⇒ to *establish* a local equation use `rule`; to *rewrite* with it use
        `subst` or chain it via `using ... by simp` (never `simp add:`).
    * `Fq3329.nat_pow_Suc` resolves to the GLOBAL `nat_pow_Suc` (no carrier
      premise), while `Fq3329.nat_pow_Suc2` is the monoid version **with** the
      `x ∈ carrier G` premise ⇒ the latter needs `using cx ...` (else that
      premise is left open: "Failed to finish proof", subgoal `x ∈ carrier Fq`).
    * `card (Units Fq)` alternative: `Fq3329.totient_eq` + `Fq3329.prime_totient_eq`
      also works (`_a7probe/M4.thy` RC=0).
    * statement-level bug to avoid: bare `[^]` in a lemma statement is illegal
      outside a group context ("Illegal reference to implicit structure") —
      always write `[^]\<^bsub>Fq\<^esub>` in the statement.
- isabelle build -D aligned: RC=0.  Counts: T0 17/0 | T1 21/**5** | T2 8/8 | T3 8/8;
  total 54 lemmas / **21** sorry (raw token 23).  bytes 21769; bom/nul/fffd/crlf=false.
- T1 remaining 5 (all blocked on undefined `consts`, not proof technique):
  `B4`, `C2`, `C6` (wait on `x1_of` / `t_of` / `adapted_of`),
  `F1_pk`, `F1_sig` (wait on `deser_pk` / `deser_sig`).
  ⇒ T1 cannot reach 0 sorry until those bodies are defined; the 7 -> 5 drop is the max
    obtainable without new definitions.

---

## Addendum 2026-10-19 01:3x -- T1 重新分层：T1-A（代数公理，16/0） vs T1-D（定义依赖，5/5）

**口径拍板（业主）**：把原单一 T1 桶按「代数恒等式 vs 协议定义层正确性」拆开 —— 这是**分类修正**，不是搬家、也不是凑数。原 37 义务表本身就把两类混在 T1 里。

- **T1-A（代数公理层）**：**16 引理 / 0 sorry**。组成 = `A1–A8`（14 引理）+ `F2`、`F3`（2 引理：签名长度 `1+4m`、u16 小端，均已闭合）。
- **T1-D（定义依赖层）**：**5 引理 / 5 sorry** = `B4` / `C2` / `C6` / `F1_pk` / `F1_sig`，阻塞于 `x1_of / t_of / adapted_of / deser_pk / deser_sig` 未定义（TODO(define)）。
- **全表口径**：**54 引理 / 21 sorry** = T0 17/0 ｜ T1-A 16/0 ｜ T1-D 5/5 ｜ T2 8/8 ｜ T3 8/8。`isabelle build -D aligned` → **RC=0**（`Finished VWZ_A3_Aligned (0:00:03)`）。

**明确不 overclaim**：本文件**不说「T1 清零」**。只并排挂两个真数 —— ①「T1-A 代数公理 0 sorry」②「全表 21 sorry（其中 T1-D 5 条如实挂账）」。`B4/C2/C6/F1` 未证是因其主语是未定义常量，非证明技术问题。

**计数口径提示**：`_count.cjs` 按 `\`section\`` 分桶，故 T1-A / T1-D 用 **`section`**（而非 `subsection`）分层；`raw sorry token` 会因正文 text 块里出现 “sorry” 字样而虚高（本次 31），**一律以分桶 `TOTAL = 21` 为准**。

---

## Addendum 2026-10-19 01:4x -- T2 开可证入口（det2），54→56 引理口径说明

- 起 `_t2probe/`（对 `VWZ_Fq3329.thy` / `VWZ_Matrix.thy` 做 **sha256 逐一核等的副本**，控制项证明确实测的是真定义），六候选全过：
  - `P1` / `P1b` / `P1c`：`det2 (id_mat 2) = 1` → **RC=0**
  - `P2` / `P2b`：`i ≠ j ⟹ det2 (row_add_matrix 2 i j f) = 1` → **RC=0**
  - `P2c`：同式 `mod 3329` → RC=0
- 落盘两条 T2 非 sorry 引理（在 B2 小节内）：
  - `T2_B2_det2_id: det2 (id_mat 2) = 1` —— `by (simp add: det2_def id_mat_def entry_def)`
  - `T2_B2_det2_rowadd: i ≠ j ⟹ det2 (row_add_matrix 2 i j f) = 1` —— `by (simp add: det2_def row_add_matrix_def entry_def split: if_splits)`
- **不动 B2 义务本体**：通用式 `T2_B2: i ≠ j ⟹ det (…) = 1` 仍是 `sorry`（`det` 未定义）。**没有把 B2 标成已证**，只新增两条 2×2 的 `det2` 入口（正是「矩阵层定义自洽」的证据）。
- **口径变化（如实）**：T2 8→10 引理（+2 入口，sorry 仍 8）；**全表 54→56 引理 / 21 sorry**。T1-A（16/0）、T1-D（5/5）不变。
- `isabelle build -D aligned` RC=0；文件 23846 B，bom/nul/fffd/crlf 全 false。

**待业主确认的一点**：② 里「替换 T2_B2 的 sorry」本轮按「不删未证义务、只加可证入口」执行（否则等于拿 2×2 特例冒充 B2 已证 = overclaim）。若你确要以 2×2 `det2` 版**替换**通用 B2 语句（则 T2 sorry 8→7、全表 21→20），说一声改。

> **已裁决（Addendum 2026-10-19 01:5x）**：接受「新增两条 det2 入口、通用 B2 保留 sorry」，不做字面替换。

---

## Addendum 2026-10-19 01:5x -- 口径修正（T1-A 表述）+ 定义层落地 · 阶段一（VWZ_Protocol.thy）

**① 口径修正（T1-A 表述）**
- 定稿表述：**T1-A = A1–A8（14 引理）+ F2、F3（2 引理）= 16 引理 / 0 sorry**。
- 去掉一切「费马桥作为独立加项」的说法（A7 本身就在 A1–A8 里，不是额外一项）。`aligned/VWZ_ObligationsAligned.thy` 的 T1-A 段说明已同步改口（不再把 Fermat 单列）。

**② 定义层落地 · 阶段一：新增 `aligned/VWZ_Protocol.thy`（仅 definition/consts，不证性质）**
依据 `fibemate-vwz-specification_20260906.md`（v0.2.0-spec）逐节落地：
- **数据模型**（§3.6 / §6）：`pkey`（`pk_k`、`pk_psi :: int list list list`）、`sigrec`（`sg_k`、`sg_w2`、`sg_w3`）、`skey`（10 字段：k、λa/λb/λc、X2a⁻¹/X3a⁻¹、M2/M3、x1、seed）。
- **`x1_of`**（§3.4）= `sk_x1 sk`（真定义，从 sk 投影）。
- **`t_of`**（§5）= `hash_target (pk_k pk) msg`；`hash_target` 仍 `consts + TODO(define)`（需 SHAKE-256 XOF + Fisher–Yates + §5.1 采样）；**§5.1 拒绝上界 `reject_bound N = (65536 div N) * N` 给了真定义**。
- **`adapted_of`**（§6.2）= `map2 (λa b. a * invmod b mod 3329) t x1`（真定义）。
- **`deser_pk` / `deser_sig`**（§8）= 按 §8.3 长度门（对单字节 `k`）+ `decode2`（LE16 解包 `lo + 256*hi`）的真定义，为 `ser_pk` / `ser_sig` 的逆（差 §8.3 长度门）。
- **`eval`**（§4）= `map (eval_slice ·) pk_psi`，`eval_slice S w2 w3 = dot w2 (matvec S w3) mod 3329`（真定义）。
- 仍为 `consts + TODO(define)`：`hash_target`（XOF），以及沿用的 `KeyGen/Sign/Verify/Eval` 等需 RNG / Gauss-Jordan 的对象。

**验收**：`isabelle build -D aligned` → **RC=0**（`Finished VWZ_A3_Aligned`）。计数不变 **56 引理 / 21 sorry**（新文件 0 引理 / 0 sorry，只有定义）。文件 4976 B，`bom/nul/fffd/crlf` 全 false；`ROOT` 已列入 `VWZ_Protocol`；`_check.cjs` 白名单已加。

**未做（留给阶段二）**：把 T1-D / T2 的义务**重新锚定**到这层定义（现有 `x1_of / t_of / adapted_of / deser_*` 的 `consts` 与义务里的 `nat list` 型别需改型；`t_of` 需补 `pk` 参数或引入 `k`），再定证明顺序。

---

## Addendum 2026-10-19 02:4x -- 阶段 2a（签名锚定）:口径 + 一处类型冲突（待裁）

**已完成的 2a 改动**（`aligned/VWZ_ObligationsAligned.thy`）：
- imports 加 `VWZ_Protocol`；删 5 条重复 `consts`（`x1_of / t_of / adapted_of / deser_pk / deser_sig`）；
- B4 语句不变（`sk` 现推为 `skey`）；C2 改 `t_of pk msg`；C6 改 `adapted_of (t_of pk msg) (x1_of sk)`；F1_pk/F1_sig 语句不变（现指向 VWZ_Protocol 的 `deser_*`）。全部保留 `sorry`。

**口径**：
- **签名锚定不算 sorry 减少**——T1-D 仍 5/5，全表仍 56/21（锚定只是把 `consts` 换成 `definition`，命题本身未证）。
- **C2 锁死**：其主语含 `t_of`，而 `t_of` 依赖 `hash_target`（XOF 未定义）→ 补 XOF 前不可证，如实留 sorry。
- **T1-D 2b 后从 5 降到几条**：不预设，取决于 2b 实际战绩。

**⚠️ 类型冲突（待裁）**：`isabelle build -D aligned` → **RC=1**。根因 = `hash_target` **被声明两次且元素型别不同**：`VWZ_Fq3329`（`nat list`，供 T0_C5 / T2_D5 / T3_C1）与新建的 `VWZ_Protocol`（`int list`）。Isabelle 取**后导入者** → `T3_C1` 的 `weight (hash_target k msg)` 报 `Clash of types "int" and "nat"`（line 498）。
- **Option A（最小修，仅动 VWZ_Protocol；已按规约先报不改）**：删 `VWZ_Protocol` 里的 `consts hash_target`，改为复用 `VWZ_Fq3329` 的 nat 版并强制转换：
  `definition t_of where "t_of pk msg = map int (hash_target (pk_k pk) msg)"`
- **已实测**：scratch 副本 `_anchorfix/` 打此补丁 → `isabelle build -D _anchorfix` **RC=0**（`Finished VWZ_A3_Aligned`）。主目录暂红，等你点头再动 `VWZ_Protocol`。

**2b 预判（定义层落地后暴露）**：B4（`0 < x1[i] < q`）、C6（`adapted=0 ⟺ t=0`）、F1_pk/F1_sig 在**无前提**下都不成立（`x1 : int list` 无约束；`psi` 长度无约束）——需 spec 侧条件（Sec 6.2 的 `x1[i] ≠ 0`；Sec 8.3 的精确长度）。2b 逐条给 RC 证据。

---

## Addendum 2026-10-19 03:1x -- Option A 已合 + 2b 口径（三类区分）

**① Option A 已落地（L1）**：`VWZ_Protocol.thy` 删重复 `consts hash_target`，`t_of` 改 `map int (hash_target (pk_k pk) msg)`。`isabelle build -D aligned` **RC=0**；计数 **56 引理 / 21 sorry 不变**（锚定不改计数）。字节体检全 false。

**② 2b 三类区分（口径）**：
| 类 | 条 | 处置 | 理由 |
|---|---|---|---|
| **加 spec 前提** | C6、F1_pk、F1_sig | 义务**语句**忠实于 spec：C6 加 `x1[i] ≠ 0`（Sec 6.2）；F1 加长度门 + `∀x∈set … x < 65536`（Sec 8.3）| 定义层落地后发现**无前提形式为假**，属义务语句 bug（录入时省略了 spec 侧条件） |
| **依赖未定义** | B4 | 语句不动，留 sorry；注释标明「依赖 KeyGen range 不变量，KeyGen 未定义」 | spec Sec 3.4 的 `x1[i] ← randrange(1,q)` 是 KeyGen 的不变量，非 x1 本身的定义性质 |
| **定义未建模** | C2 | 语句不动，锁死 | 主语含 `t_of` → `hash_target`（XOF 未建模）| 

**明确：加前提不是为了让 sorry 变少，是义务语句忠实于 spec。**

**③ 2b 执行状态（诚实报）**：上一条（探针未闭环）已被本轮推翻 —— **C6 / F1_pk / F1_sig 三条已闭环**，T1-D sorry 5→2，全表 **56/21 → 56/18**。详见下方 Addendum。

---

## Addendum 2026-10-19 10:2x -- aux 层落地 + 2b 三条闭环（T1-D 5→2，全表 56→18）

### ① aux 引理的定位（证明工具，不进义务表）

新建 `aligned/VWZ_Aux.thy`（`imports VWZ_Protocol`，已列入 `aligned/ROOT`），**`_count.cjs` 不扫描该文件** —— 方案 C。定位写进文件头：**证明工具，不是义务**；任何一条若本身是义务，必须搬回 `VWZ_ObligationsAligned` 并计数。

**三步验证（改前/改后/加 dummy）全绿**：

| 步骤 | 操作 | `_count.cjs` | build |
|---|---|---|---|
| 改前基线 | — | 56 / 21 | RC=0 |
| 加 `VWZ_Aux.thy` + ROOT 列入 | 含 `aux_dummy` | **56 / 21** | RC=0 |
| 删 `aux_dummy` | 只留真 aux | **56 / 21** | RC=0 |

⇒ aux 确实不进账。（`_check.cjs` 白名单同步加入 `VWZ_Aux.thy`。）

### ② 本轮两条硬核障碍的探针证据（如实记录）

**障碍一：`prime (3329::int)` 的 simp 自循环**
- 库规 `prime_nat_int_transfer`（`Computational_Algebra/Primes.thy:126`）标 `[simp]`，形式是 `prime (int n) ⟷ prime n`；`prime_nat_iff_prime`（`:164`）也是 `[simp]`。
- 直接 `by simp` / `simp add: prime_int_nat_transfer` 在 `prime` 目标上**不收敛**：实测 `poly` **240s CPU 超时**（rc=124，三次：`P5`/`P8`/`G2`/`A1`/`A2`）。
- **正解（RC=0）**：绕开 simp 两步走 —— 先 `prime (int 3329)` by `(subst prime_nat_int_transfer) (rule prime_3329)`，再用 `presburger` 得 `(3329::int) = int 3329` + `metis` 搬过去。落在 `aux_prime_int` / `aux_prime_int'`。
- 另证：`subst prime_nat_int_transfer` 只能匹配**字面 `int n`**，直接对 `prime (3329::int)` 用会 `Failed to apply initial proof method`（P1–P4 全败）。

**障碍二：`decode2` 的配对重索引方向**
- `decode2` 从索引 0 按对取字节，前插 2 字节会把后面每一对**整体偏移一格**；需要的形状是 `map f [0..<Suc n] = f 0 # map (λi. f (Suc i)) [0..<n]`。
- 库 `simp` 默认用 `upt_Suc` 把 `[0..<Suc n]` 拆成 `[0..<n] @ [n]`（**错方向**），残留目标形如
  `map ?g [0..<n div 2] @ [?g (n div 2)] = (a + 256*b) # map (λi. Y!(2*i) + 256*Y!(Suc (2*i))) [0..<n div 2]`（`U1`/`S1`–`S12`/`D1`/`D2`/`E1` 全 RC=1）。
- **正解（RC=0）**：不交给 simp，改为**手工 Isar 分步** —— 先把 `decode2` 展开成 `Some (map ?g [0..<Suc ?n])`，再 `by (rule map_upt_Suc)` 定向拆首，再分别证 `?g 0 = a + 256*b`（`by simp`）与尾段（`by (simp add: nth_Cons)`），最后 `by simp` 合拢。落成 `aux_decode2_cons2`。
- 归纳步另需 `a mod 256 + 256 * ((a div 256) mod 256) = a`（由 `hd: a < 65536` + `div_mult_mod_eq` + `mult.commute` + `arith`），`by simp` 与 `presburger` 都不行。

### ③ 2b 三条闭环（语句按 spec 加前提 + 证明同时落地）

| 义务 | 前提（spec 依据） | RC | 依据引理 |
|---|---|---|---|
| **C6** | `x1[i] ≠ 0`（§6.2）、`1 ≤ x1[i] < q`、`0 ≤ t[i] < q`、`length x1 = length t`（`map2` 需等长） | **0** | `aux_c6_core`（域上乘逆不产零）+ `nth_map`/`nth_zip` |
| **F1_pk** | `k < 256`（§8.3 单字节）、`length psi = par_n k * par_m k * par_m k`（§8.2）、`∀x∈set psi. x < 65536` | **0** | `aux_u16le_roundtrip` |
| **F1_sig** | `k < 256`、`length w = 2 * par_m k`、`∀x∈set w. x < 65536` | **0** | `aux_u16le_roundtrip` |

**口径**：加前提是**义务语句忠实于 spec**（无前提形式为假：`k = 300` 不进单字节；`x1[i] = 0` 时 `invmod` 无意义；元素 ≥ 65536 不可回环），不是为减 sorry。B4（依赖 KeyGen range 不变量，KeyGen 未定义）、C2（`hash_target` XOF 未建模）**保持 sorry**，注释已标明原因。

### ④ 计数（现算，`_count.cjs`）

```
T0 17/0 | T1-A 16/0 | T1-D 5/2 | T2 10/8 | T3 8/8
TOTAL lemmas = 56 | TOTAL sorry = 18     (原 21，−3)
```

`isabelle build -D aligned` **RC=0**；`_check.cjs` 全文件 bom/nul/fffd/crlf = false。

### ⑤ 剩余 T1-D 2 条为何仍 sorry

- **B4**（`0 < x1[i] < q`）：spec §3.4 的 `x1[i] ← randrange(1, q)` 是 **KeyGen 的不变量**，`KeyGen` 仍是 `consts TODO(define)`；定义层只给了 `x1_of sk = sk_x1 sk`，`sk_x1` 是 `int list` 无约束。**不能**靠加前提解决（那是把义务改成重言式），必须等 KeyGen 建模。
- **C2**（`t[i] = 0 ∨ 1 ≤ t[i] ≤ 3328`）：主语含 `t_of` → `hash_target`（SHAKE-256 XOF 未建模，仍是 `consts`），锁死。

---

## Addendum 2026-10-19 11:3x -- PR #274 关闭 + T2 `det` 定义层落地

### 一、PR #274 处置（已关闭，未合并）

关闭于 `2026-10-19T03:35:12Z`，`merged: false`。留言：<https://github.com/Lennonhaha/fibemate/pull/274#issuecomment-6259082050>。

**三条独立问题，均非「等 CI 重跑」可解**：

1. **DCO 失败是结构性的**。失败 commit `a26036af55c6` 的主题是 `Merge branch 'main' into dependabot/...` —— 这是「把 main 合进分支」产生的 merge commit，**committer = GitHub，天然无 `Signed-off-by`**，且不能原地 amend（会改写分支）。重跑必然复现。正解是 **rebase 到 main**（见规则 R：禁用 GitHub UI「Update branch」，正是同一根因）。
2. **`google/osv-scanner-action` 未锁到 release**。新 SHA `9a96bc4d…` 实测为 **`main` 的 tip**（`compare main...9a96bc4` → `status: identical`），**不属于任何 tag**。对照：`v2.6.0` = `a345acff…`，`v2.7.0` = `b1d267ae…`，而 `9a96bc4` 在 v2.7.0 之后 2 个 commit。SHA 虽不可变，但**未打 tag 的 SHA 不是被 review 过的 release**（无 release note 可审、上游未声明该状态受支持），钉在分支 tip 等于放弃 pin 的意义。
3. **分组过宽，无法作为单一决策 review**。一个 PR 捆了四类互不相关的变更：codeql-action 4.38.2→4.38.3（bundle 升 2.27.2 + 对 CodeQL ≤2.21.2 的弃用警告）、setup-java 6.0.1→6.1.0（RISC-V、Maven plugin repo、版本解析修复）、scorecard-action 2.4.4→2.5.0（**迁到 Scorecard v5.6.0 且托管服务迁新基础设施 —— 会改变已发布结果的含义**）、osv-scanner（同上）。且单一失败 check 掩盖了四个中哪个出问题。

**后续拆分（已写进留言）**：(a) codeql-action + setup-java；(b) scorecard-action（对照 Scorecard v5.6.0 release notes 单独审）；(c) osv-scanner 锁 `a345acff…`（v2.6.0）。

### 二、T2 `det` 定义层：选 Laplace，不选 Leibniz/RREF

**Leibniz 路线被库事实否决**：`HOL-Combinatorics.Permutations` 提供的是 `permutes`（**函数谓词**）与 `sign`，**没有「排列列表枚举器」**。探针 `_t2probe/L3.thy` 实测：`permutations [0..<3]` 报 **`Illegal free variable(s) in term: permutations`**（RC=1）。要自己造枚举器并证明「无重复 + 完备」，是前置的大工程。

**RREF 路线被论证否决**：高斯消元需主元搜索与 F_q 除法；除法有 `invmod`，但「剩余子矩阵某元非零，否则行列式为零」这一主元论证，正是 Laplace 递归免费给出的。且 RREF 算的是标准形而非行列式，还需额外定理把两者连起来。

**选定 Laplace（沿第一行展开）**，落在 `VWZ_Matrix.thy`：
```
definition del_col :: "nat ⇒ int list ⇒ int list" where
  "del_col j r = take j r @ drop (Suc j) r"

function det :: "mat ⇒ int" where
  "det [] = 1"
| "det (r # rs) = sum_list (map (λj. (-1)^j * r!j * det (map (del_col j) rs)) [0..<length r])"
  by pat_completeness auto
termination det by (relation "measure length") auto
```
理由：**总函数、只依赖 Main、终止测度为 `length`**（删一行严格递减，termination 立即成立）。同时保留 `det3`（3×3 展开式）作为**派生定义**，其与 `det` 的一致性是需要证的引理、不在本文件声称。

**已删除** `consts det :: "mat ⇒ int"` 占位符（原 TODO(define)）。

### 三、探针踩到的坑（如实记录）

| 坑 | 现象 | 正解 |
|---|---|---|
| `HOL-Library.Permutations` 不存在 | `Cannot load theory`，RC=2 | 实际路径 `HOL/Combinatorics/Permutations.thy`；且 ROOT 需 `sessions "HOL-Combinatorics"`（仅 `= "HOL-Number_Theory" +` 不够，两者要并列） |
| `permutations` 不是列表构造子 | `Illegal free variable(s) in term: permutations` | 放弃 Leibniz 路线 |
| `text \<open>…\<close>` 里的 `HOL-Combinatorics` | `Bad arguments for document antiquotation "text"` | 文档块内**禁写 `@{text}`/反引号**，改纯文本 |
| `by eval` 遇自由变量 | `Illegal free variable(s) in term: f, j, i` | `eval` 只认**闭项**；通用语句不能用 eval，须换具体实例 |
| `simp` 证 `prime` 自循环 | 见前一条 Addendum | 走 `subst prime_nat_int_transfer` |

### 四、计数与验收

`isabelle build -D aligned` → **RC=0**（`Finished VWZ_A3_Aligned`）。计数 **56 引理 / 18 sorry** 保持不变（T0 17/0、T1-A 16/0、T1-D 5/2、T2 15/8、T3 8/8）。

**为什么计数没变**：`det` 是**定义**不是引理；T2_B2 语句锚定到新 `det` 后**仍 sorry**（语句现已 well-formed，但「行加法不改变行列式」= Laplace 递归的多线性/交错性，未证）。新增的 5 条实例验证引理（`det (id_mat 3)=1`、三个 `row_add_matrix 3 …`、`det3` 一致性）按方案 C **放进 `VWZ_Aux.thy`**，不进义务表 —— 否则会出现「靠证据引理把 56 冲成 61」的虚高。


---

## Addendum（2026-10-19 12:2x）：`det (id_mat n) = 1` 一般情形已证 —— 13 条辅助引理落地 VWZ_Aux

### 一、结论

**`aux_det_id_mat: det (id_mat n) = 1`**（任意 `n`，非仅 3×3 实例）已完整证明，探针 `AA4` **RC=0**，落地后 `isabelle build -D aligned` **ALIGNED_RC=0**。

按方案 C，这 13 条引理进 **`aligned/VWZ_Aux.thy`**（证明工具，**不进义务表**）。义务表计数 **56 引理 / 18 sorry 不变**（T0 17/0、T1-A 16/0、T1-D 5/2、T2 10/8、T3 8/8）。

### 二、证明结构（不是"打个 eval 看看"，是真归纳）

```
aux_det_id_mat  by induction n
  基例 n=0 : id_mat 0 = [] ,  det [] = 1         (det.simps(1))
  步   n=Suc m :
    aux_id_mat_decomp   id_mat (Suc m) = (id_mat (Suc m) ! 0) # tl (id_mat (Suc m))
    aux_det_head_one_cons
        首行形如 a # as、a = 1、as 全 0  ⟹  det ((a#as) # rs) = det (map (del_col 0) rs)
        （关键：Laplace 求和中除 j=0 外每项含因子 as!(j-1) = 0 ⟹ 塌缩）
    aux_delcol_tl_id_mat  map (del_col 0) (tl (id_mat (Suc m))) = id_mat m
        （逐元素 aux_delcol_tl_row，绕开 map/upt 重写）
    ⟹ det (id_mat (Suc m)) = det (id_mat m) = 1   (IH)
```

13 条引理：`aux_sum_list_zero`、`aux_del_col_zero`、`aux_id_mat_nth`、`aux_id_mat_len`、`aux_id_mat_row_len`、`aux_tl_id_mat_len`、`aux_map_nth_id`、`aux_id_mat_decomp`、`aux_delcol_tl_row`、`aux_delcol_tl_id_mat`、`aux_sum_head_collapse`、`aux_det_head_one_cons`、`aux_det_id_mat`。

### 三、本轮新踩到的坑（AA1→AA4 四轮，全部如实记录）

| # | 现象 | 根因 | 正解 |
|---|---|---|---|
| 1 | `simp add: id_mat_def` 目标爆成整个矩阵 | 展开 `id_mat (Suc m)` 后再要同时处理 `[0..<Suc m]` 两次 | **不构造首行**：保留 `id_mat (Suc m) ! 0`，用 `aux_id_mat_nth` 给逐元素事实 |
| 2 | `text<open>…@{term "! 0 = 1"}…<close>` → `Inner syntax error at "0 = 1"` | 文档反引用里 `!` 是 `nth` 的打印形式，不是合法 term 语法 | 文档块内不写这种 term，改自然语言 |
| 3 | `text<open>…@{term map}/@{term upt}…<close>` → `Malformed command syntax` | **相邻两个 `@{term}` 用 `/` 连接**会被当成路径/记法 | 两个反引用之间必须有空格或文字 |
| 4 | `fix j` 后 `j < length …` → `incompatible operand type`（`'a` vs `nat`） | `fix j` 不锁类型，`j` 保持多态，与 `length` 的 `nat` 统一失败 | **`fix j :: nat`**，或在假设里写 `(j::nat)` |
| 5 | `r ! 0 = 1 ⟹ r ≠ []` → 目标变 `False` 却推不出 | **`[] ! 0 = undefined`**，不是矛盾；`undefined ≠ 1` 在 HOL 里**不能**由 simp 得出 | 不能从 `r ! 0 = 1` 反推非空；改把引理**陈述为 `a # as` 形式**，空行分支由调用方用长度事实排除 |
| 6 | `length r = Suc (length r - 1)` → 失败 | 减法是 `nat` 截断减法，缺 `0 < length r` | 同上——用 `cases r` 让长度直接成为 `Suc`，彻底绕开算术 |
| 7 | `by (rule aux_det_head_one_cons)` 接在中间等式后 → `Failed to apply initial proof method` | `rule` 要用**当前目标**匹配结论，中间等式不构成目标 | 显式命名 `e1`/`e2` 两条等式，再 `show ?thesis using e1 e2 by simp` |
| 8 | `rule` 对含 `<lambda>` 的 RHS 不做 beta 归约 | `det.simps(2)` 的结论是 `sum_list (map (…)<lambda>…)` | 用 `by (simp add: det.simps(2))` 让 simp 完成 beta |
| 9 | `simp only: id_mat_cons det.simps(2)` → `Interrupt_Breakdown` | 两条重写规则互为反向（`id_mat_cons` 造出 `#`，`det.simps(2)` 又要拆） | **`subst` 单向应用一次**，不用 `simp only` |
| 10 | `rule list.expand` 用于 `id_mat` | `list.expand` 要 `l = [] ∨ (∃a l'. l = a # l')` 形状 | 用 **`cases`**，并显式用长度矛盾排除 `Nil` |

### 四、口径说明（防 overclaim）

- `det (id_mat n) = 1` 是 **T2 的一个特例**，不是 T2_B2 本体。**T2_B2 仍 sorry**：「行加法不改变行列式」需要多线性 + 交错性，本轮未证。
- 因此 **T2 的 8 个 sorry 一个没减少**，全表 56/18 不变。这不是失败，是"把跳板铺好了但还没过河"。
- `aux_det_head_one_cons` 的假设是 **`as ! (j - Suc 0) = 0`**（下标偏移形式），因为 `a # as` 的 `j` 从 1 起对应 `as` 的 `j-1`。这是刻意选择：避免在假设里出现 `Suc`/`0` 混合的算术目标。


---

## Addendum（2026-10-19 13:0x）：3×3 特例试水成功 + 一般 det 的多线性第一步已证

### 一、先纠一个前提错误（重要）

**`row_add_matrix` 不是「把 f 倍第 j 行加到第 i 行」。** 读定义（VWZ_Matrix.thy:83-85）：

```
row_add_matrix m i j f =
   map (\<lambda>r. map (\<lambda>c. if r = i \<and> c = j then f else (if r = c then 1 else 0)) [0..<m]) [0..<m]
```

它是**初等矩阵 E(i,j,f)**——单位阵在 (i,j) 处填 f。所以：

- `det3 (row_add_matrix 3 i j f) = 1` 才是 T2_B2 在 3×3 的**正确**陈述；
- 用户指令里的 `det3 (row_add_matrix 3 i j f) = det3 m` 是**另一个命题**（需要对 m 取 det3），且 m 在语句里根本没出现——按字面写不成立；
- 「行加法不改变行列式」的真形式是 `det (mat_mult (E i j f) A) = det A`，那才需要多线性。

### 二、3×3 特例：simp 一个词就够了

探针 `D1–D5` 全部 **RC=0**（`_t2probe/`）：

| 探针 | 配方 | RC |
|---|---|---|
| D1 | `by (simp add: det3_def row_add_matrix_def entry_def)` | **0** |
| D2 | 同上 + `; presburger` | **0**（presburger 是多余的） |
| D3 | `by (cases i; cases j; simp_all add: ...)` | **0** |
| D4 | 六条具体实例 `det3 (row_add_matrix 3 0 1 f) = 1` … 一起 `simp_all` | **0** |
| D5 | **负控**：`det3 (row_add_matrix 3 0 0 5) \<noteq> 1` | **0** |

**结论**：3×3 上不需要任何多线性论证，展开 + `simp` 直接闭合。D5 证明这个配方不是空转（`i = j` 时确实不等于 1）。

**但这条配方不能推广**：它依赖 `3` 是字面量，六个 `entry` 全部塌成具体数字。一般的 `m` 上 `[0..<m]` 不会塌。

### 三、一般 det：多线性第一步已证（FF1 RC=0）

转到 Laplace 展开，两个真正有数学内容的步骤：

```
aux_det_head_zero : det (replicate m 0 # rs) = 0
aux_det_head_add  : length a = length b
                    ⟹ det ((map2 (+) a b) # rs) = det (a # rs) + det (b # rs)
```

探针 `FF1` **RC=0**，已落地 `aligned/VWZ_Aux.thy`（16812 → 20446 B，+3634）。`ALIGNED_RC=0`。

证明要点：
- 展开 `det.simps(2)` 得到 `sum_list (map (\<lambda>j. (-1)^j * r!j * det (del_col j rs)) [0..<length r])`；
- **首行全零**：每一项含因子 `(replicate m 0)!j = 0` ⟹ 整个 map 是 `replicate m 0` ⟹ `sum_list = 0`；
- **首行可加**：`(map2 (+) a b)!j = a!j + b!j`（需 `length a = length b`）⟹ 每项拆成两项之和 ⟹ **用库里的 `sum_list_addf`** 把 sum_list 拆开。

### 四、本轮踩的坑（补 11–16）

| # | 现象 | 根因 | 正解 |
|---|---|---|---|
| 11 | `text \<open>…@{term "i = j"}…<close>` → `Malformed command syntax` | 文档块里 `=` 后面的内容被当反引用参数解析 | **文档块一律不写 `@{term}`**，改纯文本。BB2/BB3 连挂两轮都因为这个 |
| 12 | `text \<open>…@{thm sum_list_addf}…<close>` 同样炸 | `thm` 反引用在 `text` 里也不稳 | 同上 |
| 13 | 自己证 `sum_list (map (\<lambda>x. f x + g x) xs) = …` 用 `simp_all`/`ac_simps` 都差一步 | 加法重结合方向 | **库里有 `sum_list_addf`**（Groups_List.thy:271，`comm_monoid_add` locale）——**别重造** |
| 14 | `rule sum_list_addf` 直接可用 | 它是 locale 引理，但在 `int` 上实例化正常 | 直接 `by (rule sum_list_addf)` |
| 15 | 用正则剥 `text` 块把整个文件删成 5 行 | `/^\s*text\s*\\<open>/` 在 Node 字符串里反斜杠层数算错 | 别写这种脚本；**直接重新生成文件**更安全 |
| 16 | 共享探针头里的辅助引理挂了，导致 5 个候选**全报同一行错** | 一个 `rm_entry` 失败 → 后续全部不可判 | **每候选独立成文件、不含共享前置引理**，否则 RC 全是假阴性 |

### 五、计数与口径

`ALIGNED_RC=0`。义务表 **56 引理 / 18 sorry 不变**（T0 17/0、T1-A 16/0、T1-D 5/2、T2 10/8、T3 8/8）。`VWZ_Aux.thy` 现 20446 B，含 15 条证明工具（13 条 det-id + 2 条多线性），按方案 C **不进义务表**。

**T2_B2 仍 sorry。** 已证的是它的两个**构件**（首行全零、首行可加），不是本体。要闭合 T2_B2 还差：
1. 交错性（交换两行 ⟹ det 变号）——或者直接用「首行可加 + 首行全零」推出「加 f 倍某行到首行不变」；
2. 把首行的结论推广到任意行（需要「交换行」或行置换）。

**不预设 T2 剩余 sorry 数。**
<!-- seg: _seg-brief5-d58fb3562875 -->
## Addendum 2026-10-19（下午）：`aux_det_zero_row` 闭环 + T2 跳板就位 + CBOM 首刀

### 一、`aux_det_zero_row` 证明通过（RC=0）

**目标**：`zhas M ⟹ det M = 0`（含全零行 ⇒ 行列式为 0，**不要求方阵**）。

**为什么必须长度归纳**：递归步的 IH 要作用于 `map (del_col j) rs`，它不是 `r # rs` 的**结构子项** ⇒ 结构归纳（`induct M`）到不了。这是此前 Z7/Z8 反复失败的数学层根因。

**三个 Isar 陷阱（逐一实证后修正）**：

| # | 现象 | 根因 | 正解 |
|---|---|---|---|
| 1 | `Failed to apply initial proof method`，goal 为 `zhas M ⟹ det M = 0` | `length_induct` 要求目标是**项级应用** `P M`，Pure 蕴含形式不匹配 | 改 `nat_less_induct` + `arbitrary: M` |
| 2 | `?M = r # rs ⟹ …` 或 `r = replicate (length r) 0 ? …`，任何 tactic 都关不掉 | `arbitrary: M` 下外层 `show ?case` 含 **schematic `?M`**；嵌套 `cases` 里 `?thesis` 解析成该 schematic 形式 | **嵌套块不用 `?thesis`**，写显式目标 `show "det (r # rs) = 0"`，再用 `M_eq` 改写 |
| 3 | `?x∈{0..<length r}. r ! x = 0 ∨ det … = 0 ? (∑…) = 0` | `using eq by simp` 把等式当 **rewrite 规则**，在 `sum_list` 上生成新子目标 | 用 `arg_cong[OF eq]` 在 `sum_list` 下改写，再 `also … finally` |

**落盘位置**：`aligned/VWZ_Aux.thy`（方案 C，**不进义务表**），新增 5 条：
`zrow`/`zhas` 定义、`aux_zrow_iff`、`aux_zrow_replicate`、`aux_zrow_del_col`、`aux_zhas_map_del_col`、`aux_det_zero_row`。
文件 20446 → 25865 B（+5419），bom/fffd/crlf 全 false。

**计数不变**：`isabelle build -D aligned` RC=0；义务表仍 **56 引理 / 18 sorry**。**这是跳板，不是过河** —— T2 的 8 个 sorry 一个未减。

### 二、T1-D 注释纠偏（真进度，非回退）

`_count.cjs` 现算 T1-D = **5 引理 / 2 sorry**（B4、C2），文件头注释原写「5 sorry」已过时 —— stage 2b 已证 C6/F1_pk/F1_sig。
已同步文件头 + section 标题（`5 sorry` → `2 sorry`；T2 的 `8 lemmas` → `10 lemmas`），**字节数 27802 不变**（等长替换），build RC=0。

**纪律**：计数以 `_count.cjs` 现算为准，**注释是线索不是结论**。

### 三、CBOM 第一刀（L1，未 commit）

**能力早已存在**（非从零）：`scripts/build-cbom.js`（CycloneDX 1.6）、`tools/cbom-cyclonedx.json`、`tools/cbom-diff.js`、`tools/scan-crypto-assets.cjs`、`www/docs/cbom-viewer.html`。

**硬伤 1（已修）**：`build-cbom.js` 写死 `C:/temp/fibemate-clone/...`（1 处输入 + 2 处输出）⇒ 换机/CI 直接跑不了。
改成 `path.resolve(__dirname,'..')` + `path.join(ROOT,…)`，diff 仅 4 行（+2 −2 语义，另 +1 require / +1 ROOT）。

**硬伤 2（待办）**：无 CI 步骤、无 Release 产物挂载、**无官方 schema 校验** —— 与 10-03 教训（内部全绿、José 用官方 CLI 验出 21 条全错）同型。

**官方 schema 校验（目标达成）**：
```
TARGET = D:\FIBEMATE\fibemate\tools\cbom-cyclonedx.json
BOM bytes = 61901
specVersion = 1.6  components = 9
VALID = true
RC = 0
```
校验器：`fibemate-tools/cbom-tools` 的 **ajv 8.20.0** + `test/fixtures/bom-1.6.schema.json`（262666 B）+ `jsf-0.82` + `spdx`。

**计数口径纠偏**：`algorithms: 12` ≠ `components: 9`。`Double-Ratchet` / `NTT` / `TLA+` **不是密码算法**（协议/数学工具），归入 `excluded`，只输出 9 个 `cryptographic-asset`。**报数必须说清是「扫描到的算法标签数」还是「CBOM 组件数」。**

### 四、并发告警（重要）

2026-10-19 **14:17** 另一会话在本仓并发作业：整体重写 `scripts/build-cbom.js`（10718 → 16686 B，371 行插入）、新建 `tools/validate-cbom.cjs`（3842 B）、把 `docs/CONTRIBUTORS-GUIDE.md` 由未跟踪改为已暂存。
**对方版本更强**（确定性 serialNumber/内容哈希、`SOURCE_DATE_EPOCH` 可复现、`--check` 模式、`fibemate:` 命名空间、自带校验器），**我不覆盖它**。

**纪律**：同 workspace 多会话并发时，**改前必 `git status -sb` + 查文件 mtime**，勿凭「刚才是这样」下结论（与「三个前查」同族）。

### 五、当前状态

| 层 | 状态 |
|---|---|
| `isabelle build -D aligned` | **RC=0** |
| 义务表 | 56 引理 / 18 sorry（T0 17/0、T1-A 16/0、T1-D 5/2、T2 10/8、T3 8/8） |
| `VWZ_Aux.thy` | 25865 B，含 `aux_det_zero_row` 全套（方案 C，不进义务表） |
| CBOM | 路径已修、生成成功、官方 schema **VALID=true**，未 commit |
| 下一步 | 用 `aux_det_zero_row` 攻 `aux_det_elementary`（初等矩阵 det=1），才真正动 T2 的 sorry |
<!-- seg: _seg-brief6-dd8f6ce20085 -->
## Addendum 2026-10-19（15:55）：T2_B2 i=0 分支完整闭环

### 结果

`aux_el_det_elementary_i0` 已完整证明并并入 `aligned/VWZ_Aux.thy`：

```
0 < m ⟹ 0 < jc ⟹ jc < m ⟹ det (row_add_matrix m 0 jc f) = 1
```

验证：`isabelle build -c -D aligned` → `Cleaned → Running → Finished VWZ_A3_Aligned (0:00:06)`，`ALIGNED_RC=0`（全量重编译，非缓存）。文件 25865 → 39323 B（+13458），bom/nul/fffd/crlf 全 false。

### 计数（现算）

```
T0 17/0 ｜ T1-A 16/0 ｜ T1-D 5/2 ｜ T2 10/8 ｜ T3 8/8
TOTAL 56 lemmas / 18 sorry   （raw token 31）
```

`aux_el_*` 按方案 C 不计入义务表，故 **T2 的 8 个 sorry 未减少**，`T2_B2` 主陈述仍 sorry。这是诚实的账：**新增的是可复用的 i=0 部件，不是义务闭环**。

### 证明结构（Laplace 沿首行 + 塌缩）

1. 首行 `hd E = e_0 + f·e_jc`（`aux_el_row0`），`tl E = tl (id_mat m)`（`aux_el_tl`）。
2. Laplace 展开 `det E = Σ_k (-1)^k · r0!k · det (minor k)`。
3. 逐项归零（`aux_el_collapse_var`）：k>0 时，`k ≠ jc ⇒ r0!k = 0`；`k = jc ⇒ det (minor jc) = 0`（余子式含全零行，走 `aux_det_zero_row`）。
4. 只剩 k=0 项：`r0!0 = 1`，`minor 0 = id_mat (m-1)`（`aux_el_minor0`），`det (id_mat (m-1)) = 1`。
5. 故 `det E = 1`。

### 三个库机制坑（已记 TOOLS.md）

- `upt_Suc` 无条件把 `[0..<Suc n]` 拆成 `@[n]` → nth 分支爆炸。**解法：全用变量 m + `0 < m` 前提**，让 Suc 形态不出现。
- `replicate` 拼接：`simp add: replicate_add` / `rule [symmetric]` / `subst` / `metis` 全败。**解法：`nth_equalityI` 逐位证**。
- `map_upt_Suc` 是前缀式（`[0..<Suc n]`），不能做索引移位。**解法：自写 `aux_el_shift_unit`**。

### i>0 的下一步（待做）

需拆两种情形：

- **j > 0**：`map (del_col 0) (tl (row_add_matrix m i j f)) = row_add_matrix (m-1) (i-1) (j-1) f`，套对 m 的归纳假设。
- **j = 0**：`j-1` 在 nat 退化，恒等式不成立。此时余子式删去第 0 行第 0 列后，原第 i 行第 0 列的 f 落在新矩阵的第 (i-1) 行第 0 列 → 仍应得到 `row_add_matrix (m-1) (i-1) 0 f`（列不变，因为删的是第 0 列之前的列不存在，需单独核）。

### 未做的 PR（阻塞）

`plans/` 在 workspace 仓库中**未跟踪**（0 tracked），而 workspace 仓库 remote 指向 `Lennonhaha/fibemate` 且带 **425 个暂存删除**。`fibemate` 主仓无任何 `.thy`；`fibemate-wt-lg`（`experimental/vwz-lg`）也无 `.thy`。**VWZ Isabelle 工作目前无远端归属**，PR 目标需业主指定。

<!-- seg: t2b2-closed-20261019 -->
## Addendum (2026-10-19, later): T2_B2 closed

**Result.** `T2_B2` is now a proved lemma, not a `sorry`:

```
lemma T2_B2: "i \<noteq> j \<Longrightarrow> det (row_add_matrix m i j f) = 1"
```

Ledger moved from 56 lemmas / 18 `sorry` to **56 lemmas / 17 `sorry`**
(T2: 8 -> 7). Obligation count is unchanged at 37: the new support lemmas are
tooling (scheme C), not obligations.

**Why the statement needs no side conditions.** This was the open question at
the end of the previous session. If `i >= m` or `j >= m`, the index never
matches any row or column index in `[0..<m]`, so `row_add_matrix` performs no
substitution at all and returns `id_mat m` verbatim. `det (id_mat m) = 1`, so
the out-of-range cases are *true*, not merely vacuously excluded. No
`i < m` / `j < m` hypothesis is required.

**Proof shape** (induction on `m`, generalised over `i j f`):

| Case | Reduction | Closed by |
|---|---|---|
| `i >= m` or `j >= m` | degenerates to `id_mat m` | `aux_t2_nofire_i` / `aux_t2_nofire_j` + `aux_det_id_mat` |
| `i = 0`, `j > 0` | elementary row addition on row 0 | `aux_el_det_elementary_i0` |
| `i > 0`, `j = 0` | minor at (0,0) is `id_mat (m-1)` | `aux_t2_minor0_j0` |
| `i > 0`, `j > 0` | minor at (0,0) is `row_add_matrix (m-1) (i-1) (j-1) f` | `aux_t2_minor0_jpos` + IH |

The `i > 0` cases both begin with `aux_t2_head_reduce`: row 0 of the matrix is
the pure unit row `e_0` (because the substitution sits on row `i > 0`), so the
Laplace expansion collapses to the single `(0,0)` minor.

**Two technical lessons.**

1. `arith` and `simp` both fail on boolean index equivalences such as
   `(r = i) = (r - 1 = i - 1)`. Splitting into `0 < i` and `0 < r` is not
   enough. The working form is a `cases` split on the left-hand side, proving
   each branch by `simp` with the relevant positivity facts in scope.
2. `Suc 0 + k` and `Suc k` are *not* the same term to the simplifier. If the
   target mentions `Suc k`, the helper equation must be stated as
   `(Suc 0 + k = j) = (k = j - Suc 0)`, not as an equation about `Suc k`.

**Repository.** The artifacts live in `Lennonhaha/vwz-formalization`
(commit `dffdf0d`), deliberately separate from the FIBEMATE product
repositories.

<!-- seg: rref-scope-20261019 -->
## Addendum (2026-10-19): elementary row operations, and what RREF cannot do

### What was added

`aligned/VWZ_RREF.thy` (9,257 B, **zero `sorry`**) introduces the two
elementary operations that were still missing and proves their structural
laws:

| Lemma | Statement |
|---|---|
| `aux_rref_swap_self` | `row_swap_matrix m i i = id_mat m` |
| `aux_rref_swap_comm` | `row_swap_matrix m i j = row_swap_matrix m j i` |
| `aux_rref_scale_one` | `row_scale_matrix m i 1 = id_mat m` |
| `aux_rref_swap_nofire` | out-of-range indices leave `id_mat m` |
| `aux_rref_scale_nofire` | same, for scaling |
| `aux_rref_scale_zero_row` | scaling a row by 0 yields `replicate m 0` |
| `aux_rref_det_scale_zero` | that row forces `det = 0` |
| `aux_rref_map_zero_replicate` | pointwise-zero map is a `replicate` |
| `aux_rref_sum_single` | `sum_list (map (\k. if k = i then x else 0) [0..<n]) = x` |
| `aux_rref_dot_unit` | dot of two unit-like vectors is `a*b` on the diagonal |

The session builds clean (`isabelle build -D aligned`, exit 0) and the ledger
is unchanged: **56 lemmas / 17 `sorry`**, because these are tooling lemmas and
do not enter the obligation table.

### What RREF cannot do here -- the honest part

Choosing route A was justified by "RREF will close the remaining T2
obligations". That expectation does **not** survive contact with the code, and
the reason is worth recording precisely.

Every open T2 obligation is stated about an **uninterpreted constant**:

| Lemma | Subject | Declaration |
|---|---|---|
| `T2_B3` | `X2a X2b X3a X3b` | `consts X2a :: mat` (no body) |
| `T2_B5` | `M2 M3` | `consts` |
| `T2_B7` | `psi_slice` | `consts psi_slice :: nat list => nat => mat` |
| `T2_D4` | `rows3_of` | `consts` |
| `T2_D5` | `Eval`, `Sset` | `consts` |
| `T2_D6` | `P2a P2b Zset` | `consts` |
| `T2_D1` | `Sign`, `Eval` | `consts` |

A `consts` declaration fixes a value but supplies **no property**. So
`invertible X2a` is not merely unproved -- it is **independent**: neither it
nor its negation follows from the current theory. A RREF algorithm would give
`mat_rank` and `dim_nullspace` real definitions, but it would still say
nothing about what `X2a` *is*, so `mat_rank (psi_slice pk i) = 2` would remain
underivable.

Two negative controls in the probe suite make this concrete:

- `r2_zero_not_invertible`: the zero matrix is **not** invertible, so
  "invertible" is not a trivial property that could be assumed of any matrix.
- `r4_not_all_invertible`: `~(\<forall>A. invertible A)` -- proved, so the
  universal schema fails and the constant instance cannot be obtained by
  generalisation either.

**Conclusion.** The remaining 7 T2 obligations are blocked on the *definition
layer*, not on linear-algebra machinery. Closing them requires defining
`X2a`, `X2b`, `X3a`, `X3b`, `M2`, `M3`, `rows3_of`, `psi_slice`,
`P2a`, `P2b`, `Sset`, `Zset` from the specification (Sec 6.4), which is a
specification-transcription task, not a proof task. The same holds for T1-D's
`B4` / `C2` (`KeyGen`, `hash_target`) and all of T3.

This is recorded rather than glossed because a ledger that reports 17 `sorry`
without saying *why* invites the reader to assume the gap is proof effort.
It is not.

### Method note

The probe files (`_rrefprobe/R1..R4`) are scratch and stay out of the
repository. Only the proved content moved into `aligned/VWZ_RREF.thy`; the
three inverse laws that were still `sorry` in the probes
(`r2_rowadd_inverse`, `r2_swap_inverse`, `r2_scale_inverse`) were **not**
copied across, so the shipped file has no `sorry` at all.
<!-- seg: seg-rref-4e2669767f48 -->
﻿### 2026-10-20 -- Gauss-Jordan lands; T2_B7 turns out to be a statement defect

`VWZ_RREF.thy` now carries a fuel-parameterised reduction. Fuel (`rref_fuel
f r c A`) makes the recursion structural, so termination is free; the bound
`n_rows * n_cols + n_rows + 1` covers the worst case. `mat_rank` and
`dim_nullspace` are definitions now, not `consts`, so the T2 obligations that
mention them are no longer statements about uninterpreted functions.

Five `by eval` lemmas are the evidence the definitions compute (identity 2x2,
singular 2x2, a 3x3 of full rank, the same 3x3 with a zero row, and the
nullspace count). They also pin down a shape: a 3x3 slice with one zero row
gives rank 2, which is the shape T2_B7 wants.

What is *not* claimed: that `rref` reaches a normal form, or that `mat_rank`
equals the field rank. Both are theorems, both are unproved, and the README
says so. The definition is honest (it computes what it says) without being a
correctness claim.

`mat_inv` and `mat_solve` stay undefined: both need the augmented-matrix solve,
which is the next piece of work, not a by-product of this one.

#### T2_B7 is a statement defect, not a proof gap

With `mat_rank` defined, `T2_B7: mat_rank (psi_slice pk i) = 2` can be looked at
properly, and it does not survive the look. `pk` is a bare `pkey` record, so it
ranges over every value of `pk_psi`. As soon as `psi_slice` gets the body the
spec wants (`pk_psi pk ! i`, or any projection), the claim is false for a zero
slice. There is no `i < n` either.

So the obligation is missing a well-formedness hypothesis (pk in the image of
`KeyGen`). That is a *spec* defect; fixing it silently inside the ledger would
be the same species of error the paper is about -- a statement made true by
choosing the statement. It is recorded here and in the README, and the
statement is left as it is until the spec is corrected.

Counts after this change: ledger 56 lemmas / 17 sorry (unchanged -- the
unfolding lemma lives in `VWZ_RREF`, since a definitional unfolding is not an
obligation and counting it would inflate the ledger). Repository: 10 theory
files, 191 lemmas, 1 theorem, 17 sorry, 132,006 bytes.

<!-- seg: aligned-rref-landing-20261020 -->
