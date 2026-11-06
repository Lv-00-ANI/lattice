import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
assert lines[85].startswith('/-- **T4.2'), lines[85]
assert lines[89].endswith('**'), repr(lines[89])
lines[89] = lines[89] + ' -/'
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
print('closed T4.2 docstring')