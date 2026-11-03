/-
# The spatiotemporal runtime slice

**This layer exists because the audit found that T5-T8 had NO carrier.**
**T5/T6 were strings in `open_targets`; T7/T8 were not even that.**

**Five files, one property each:**

| file | property | theorem |
|:--|:--|:--|
| `Model.lean` | one effect is reversible | `undo_apply` |
| `Seq.lean` | a sequence is reversible | `undoSeq_apply` |
| `Dep.lean` | a live plugin's dependency cannot be unloaded | `deactivate_before_unload` |
| `Confluence.lean` | disjoint effects commute | `apply_comm` |
| `Fail.lean` | a failure changes nothing | `fail_leaves_state` |

**The slice does NOT depend on `Lattice.Compose`.** **`Compose` proves the Kleisli algebra of `Option`
(`bind_assoc`, the unit laws), which is the algebraic skeleton of sequencing; this slice adds the STATE,
the INVERSE and the DEPENDENCY GRAPH that the four target statements actually need.**
**=> the two are complementary, and earlier rounds' claim that `Compose` supported these targets was
overstated -- corrected here rather than repeated.**
-/

import Lattice.Plugins.Runtime.Spatiotemporal.Model
import Lattice.Plugins.Runtime.Spatiotemporal.Seq
import Lattice.Plugins.Runtime.Spatiotemporal.Dep
import Lattice.Plugins.Runtime.Spatiotemporal.Confluence
import Lattice.Plugins.Runtime.Spatiotemporal.Fail
