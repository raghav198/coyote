import os

count = lambda op, code: sum(map(lambda l: op in l, code))
lines = ['Benchmark,Scalar Add,Scalar Subtract,Scalar Mul,Vector Add,Vector Subtract,Vector Mul,Rotate,Blend\n']
for benchmark in os.listdir('outputs/'):
    scal = open(f'outputs/{benchmark}/scal').read().splitlines()
    vec = open(f'outputs/{benchmark}/vec').read().splitlines()

    smul = count('*', scal)
    ssub = count('-', scal)
    sadd = count('+', scal)

    vmul = count('*', vec)
    vadd = count('+', vec)
    vsub = count('-', vec)
    vrot = count('>>', vec)
    vblend = count('blend', vec)
    lines.append(f'{benchmark},{sadd},{ssub},{smul},{vadd},{vsub},{vmul},{vrot},{vblend}\n')

    print(f'{benchmark}:\t({smul} *, {sadd} +)\t->\t({vmul} *, {vadd} +, {vrot} >, {vblend} @)')

open('ops.csv', 'w').writelines(lines)
