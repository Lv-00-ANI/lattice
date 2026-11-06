import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
t = io.open(p, encoding='utf-8').read()
opens = t.count('/--')
closes = t.count('-/')
print('open /--:', opens, ' close -/:', closes)
# find docstring blocks that never close
lines = t.split('\n')
depth = 0
for i, ln in enumerate(lines):
    if '/--' in ln: depth += 1
    if '-/' in ln: depth -= 1
    if depth < 0:
        print('unbalanced at line', i+1, ':', ln[:60]); depth = 0
print('final depth:', depth)