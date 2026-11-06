import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
# Drop the T4.2 explanatory block (lines 33..38, 1-based) -- it has no theorem.
assert lines[32].startswith('/-- **T4.2'), lines[32]
out = lines[:32] + lines[38:]
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(out))
print('dropped the T4.2 block')