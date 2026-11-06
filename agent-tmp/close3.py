import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
# Line 90 (index 89): split the trailing ' -/' onto its own line.
if lines[89].endswith('** -/'):
    lines[89] = lines[89][:-3]
    lines.insert(90, '-/')
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
print('moved -/ to its own line')