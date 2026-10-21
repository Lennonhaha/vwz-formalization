# ChinaXiv 提交信息表（待本人核对后填报）

> 本文件只汇总**已核验**的信息，供填报时逐项复制。标注「待补」的项需本人提供，
> 不得由脚本或助手代为猜测。

## 基本信息

- **标题**：基于 Isabelle/HOL 的 VWZ 后量子密码协议形式化验证与规范缺陷分析
- **英文标题（建议，可选）**：Formal Verification of the VWZ Post-Quantum Construction in Isabelle/HOL, and Four Defects Found by Machine in Its Specification
- **作者**：刘天赫
- **单位**：独立研究者
- **邮箱**：research@fibemate.net
- **ORCID**：待补（ChinaXiv 建议填写）
- **日期**：2026 年 10 月
- **语种**：中文
- **分类建议**：计算机科学技术 → 密码学（ChinaXiv/arXiv 对应 `cs.CR`）

## 摘要（296 字，汉字 258 + 中文标点 38；硬限 300）

后量子密码实现涉及模算术、矩阵代数与采样器，仅靠测试无法保证其数学陈述正确。本文用
Isabelle/HOL 对后量子构造（VWZ）的代数骨架与协议对象建模，并坚持一条纪律：先按原文
形式化，机器否证后才允许改述。依此在规范中发现四处缺陷：算术域错配（T2_B3）、零化度
口径错配（T2_D4），以及两处前提缺失致陈述为假（T2_B7 缺秩前提、T2_D5 迫使目标位与
消息无关）。前两处给出改述与闭合证明；后两处给出三行以内的机器反证，并区分两类不可证
原因：缺数学、缺建模决策。系统含 20 个理论文件、56 条义务引理（余 7 个未闭合，账本外
零个 sorry），构建约 16 秒。本文的贡献在于：形式化能在实现之前把"看起来对"的句子变成
"机器判定为假"的句子。

## 关键词

后量子密码；形式化验证；Isabelle/HOL；规范缺陷；矩阵代数

## 复现材料（审稿人可直接验证）

- **代码仓库**：https://github.com/Lennonhaha/vwz-formalization （**public**，已核实）
- **提交**：`0711a79`（论文入库）/ 仓库 HEAD 见 `git rev-parse HEAD`
- **构建**：
  ```
  isabelle build -D aligned -o document=false     # 期望 RC=0，约 16 秒
  node tools/count-obligations.cjs                # 56 lemmas, 7 sorry, outside 0
  ```
- **缺陷证据文件**：`aligned/VWZ_Refutations.thy`（参与同一会话构建，每次编译重新检查）

## 声明项（需本人确认后勾选）

- [ ] 本文未在其他期刊/会议发表，亦未同时投稿（预印本除外）
- [ ] 同意 ChinaXiv 公开发布（CC BY 4.0 或按平台默认许可）
- [ ] 无利益冲突；无资助项目需声明
- [ ] 数据与代码可用性声明如上（已核实仓库公开可访问）

## 提交前最后一轮机器核验结果（2026-10-21 22:2x）

| 检查项 | 结果 |
|---|---|
| PDF 总页数 | **9 页**（`main-zh.log`：`Output written on main-zh.pdf (9 pages)`） |
| 编译错误 | 0（`! LaTeX Error` 检索为空） |
| Overfull box | 0 |
| 未定义引用 | 0（两遍编译后） |
| 摘要字数 | 汉字 258 + 标点 38 = **296 ≤ 300** |
| 中文乱码 / U+FFFD / PUA | 0 / 0 / 0 |
| 仓库可见性 | public（`gh api` 实测 `private=false`） |
| 工作树 | 干净，HEAD 已推送，本地 = 远端 |
| 参考文献 | 11 条（3 条国内期刊为注释占位，待检索后补） |
