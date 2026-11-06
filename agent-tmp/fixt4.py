import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
for i, ln in enumerate(lines):
    if ln.startswith('What T4.2 needs is the property'):
        lines[i] = 'What T4.2 needs is the property, and \Lattice.Core.Repair.progress\ provides exactly it, for every \Repair\. -/'
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
print('fixed')