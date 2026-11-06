import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
t = io.open(p, encoding='utf-8').read()
# Find the module docstring (starts at /-! on line 5) and the namespace line.
head_end = t.index('namespace Lattice.Core.IR')
body = t[head_end:]
DOC = (
'/-!\n'
'# Core/IR/T4Repair.lean -- T4 over the IR: progress, convergence, fixed point (round 187)\n'
'\n'
'T4 asks three things: repair_progress, loop_converges, conj_loop_fixed_point.\n'
'All three follow from Lattice.Core.Repair, whose fields are Sat, fix, mu, absorbs, decreases, atomic.\n'
'That structure already existed; this file builds on it rather than beside it.\n'
'\n'
'The relation between atomic and decreases, which the discipline requires be stated:\n'
'decreases lowers mu at every failing point; atomic says a zero mu cannot be failing.\n'
'Without atomic, mu could reach 0 while Sat never holds, and decreases would have nothing to say.\n'
'That is what atomic_is_the_base_case states below.\n'
'-/\n\n'
)
io.open(p, 'w', encoding='utf-8', newline='\n').write('import Mathlib\nimport Lattice.Core.IR.Obligations\nimport Lattice.Plugins.Core.Repair.Repair\n\n' + DOC + body)
print('rewrote the header')