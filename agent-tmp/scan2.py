import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
# Report every line containing /- or -/ with its index, to see the true structure.
for i, ln in enumerate(lines):
    if '/-' in ln or '-/' in ln:
        print(i+1, repr(ln[:80]))