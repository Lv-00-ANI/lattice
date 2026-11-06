import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
# Line 93 (index 92) is bare text after the docstring closed; drop it.
out = []
for i, ln in enumerate(lines):
    if i == 92 and ln.startswith('What T4.2 needs is the property'):
        continue
    out.append(ln)
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(out))
print('dropped the stray line')