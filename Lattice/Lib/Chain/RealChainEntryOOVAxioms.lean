import Lattice.Lib.Chain.RealChainEntryOOV
/-!
# LATTICE: RealChainEntryOOVAxioms -- 入口桥/OOV 交付的 axiom footprint（可复现探针）

## 为什么这个文件存在

Z04 §三 F4 实测：Y12 声称的「`#print axioms` × 11 无 sorryAx」
在仓库里**没有任何可运行的载体**（探针是临时文件、已删）⇙ 按判据 14 应标 `NOT-REPRODUCIBLE`。
本文件把探针**落盘并注册 roots**，使该读数**可重跑**。

## 判据 7 的双条件（不可拆）

本文件的价值**取决于**同批 `lake build RealChainEntryOOVAxioms` 返回 `exit 0`。
单独读 `#print axioms` **不是判据**（编译失败时它仍打印看似干净的条目）。
-/

namespace Lattice

/-! ## 一、入口桥（缺口 (b)） -/

#print axioms e2e_path_exists_str
#print axioms runChainStr_eq

/-! ## 二、OOV 分词器（缺口 (c)） -/

#print axioms tokAuxV_VAll_eq
#print axioms tokenizeV_VAll_eq_tokenizeRaw
#print axioms tokenizeV_Vzz_in
#print axioms tokenizeV_Vzz_blocks
#print axioms tokenizeV_can_fail
#print axioms tokenizeV_VAll_accepts_where_Vzz_blocks
#print axioms tokenize_never_none_fails_for_tokenizeV

end Lattice
