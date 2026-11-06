import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\REPAIR-CENSUS.md'
lines = io.open(p, encoding='utf-8').read().split('\n')
for i, ln in enumerate(lines):
    if ln.startswith('| B. '):
        lines[i] = ln.replace('| 22 | **63** |', '| 23 | **66** |')
        print('updated line', i+1, '->', lines[i])
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))