import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
# Line 91 (index 90) opens ** and never closes it before the block ends.
for i, ln in enumerate(lines):
    if ln.startswith('obligation is discharged by the STRUCTURE'):
        lines[i] = ln.rstrip()
        if not lines[i].endswith('**'):
            lines[i] = lines[i] + '**'
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
print('fixed')