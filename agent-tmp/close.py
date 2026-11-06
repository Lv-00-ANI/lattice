import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
assert lines[4].strip() == '/-!', lines[4]
assert lines[68].endswith('**'), lines[68]
lines[68] = lines[68] + ' -/'
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
print('closed the header block')