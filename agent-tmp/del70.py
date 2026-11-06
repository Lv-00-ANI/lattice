import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\T4Repair.lean'
lines = io.open(p, encoding='utf-8').read().split('\n')
del lines[69]
io.open(p, 'w', encoding='utf-8', newline='\n').write('\n'.join(lines))
print('deleted line 70')