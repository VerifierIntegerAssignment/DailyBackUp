import wadze

with open('test/test1.wasm', 'rb') as file:
    data = file.read()

module = wadze.parse_module(data)

# If you also want function code decoded into instructions, do this
module['code'] = [ wadze.parse_code(c) for c in module['code']]

for exp in module['code']:
    for inst in exp.instructions:
        print(inst)
