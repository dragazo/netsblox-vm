import re

def counter():
    v = -1
    def f():
        nonlocal v
        v += 1
        return v
    return f

path = 'src/bytecode.rs'
with open(path, 'r') as f:
    content = f.read()

c = counter()
content = re.sub(r'\d+ => read_prefixed!', lambda m: f'{c()} => read_prefixed!', content)
c = counter()
content = re.sub(r'=> append_prefixed!\(\d+', lambda m: f'=> append_prefixed!({c()}', content)

with open(path, 'w') as f:
    f.write(content)
