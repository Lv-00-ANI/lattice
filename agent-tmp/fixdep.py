import io
p = r'C:\Users\xingg\Desktop\agent\lattice-new\Lattice\Core\IR\Depends.lean'
t = io.open(p, encoding='utf-8').read()
old = '''  intro i hi
  have hi' : i = (o, ix) := by simpa using hi
  rw [hi']
  exact h'''
new = '''  intro i hi
  have hieq : i = (o, ix) := by simpa using hi
  rw [hieq]
  exact h'''
t = t.replace(old, new)
io.open(p, 'w', encoding='utf-8', newline='\n').write(t)
print('fixed')