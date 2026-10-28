import Lattice.Runtime.ProgramAST

/-!
# 迁移别名：本文件已搬到 `Lattice/Runtime/ProgramAST.lean`

按 `DIRECTORY-DESIGN.md` §2.8：`git mv` 只改**模块路径**，不改声明名；
旧路径**留一个 `import` 别名**，让既有 `import Lattice.Lift.ProgramAST` 继续可用。

**namespace 仍是 `Lattice.Lift.ProgramAST`**——同样是 §2.8 的要求（不改声明名）。
所以这个文件里**没有任何声明**，只有一条 `import`。**它不构成第二个真相源。**

**它会在下一个周期删除**；届时所有 `import Lattice.Lift.ProgramAST` 都要改成新路径。
目前只有 `Lattice/Lift.lean` 引用它。
-/
