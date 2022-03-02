## Create a cpp function that compares bit strings in base 2
## 

def ite(op1, op2, cond1, cond2):
    l = 20
    d_prime = 10
    p = 2
    return cond1 * LT(op1, op2, l, d_prime, p) + cond2 * (1 - LT(op1, op2, l, d_prime, p))

def LT(a, b, l, d_prime, p):
    SUM = 0
    LocalSUM = 0
    for i in range(0, l-1):
        LocalSUM += LTsd(a[i], b[i], d_prime, p)
        LocalPRODUCT = 1
        for j in range(i + 1, l-1):
            LocalPRODUCT *= EQsd(a[j], b[j], d_prime, p)
        SUM += LocalSUM * LocalPRODUCT
    return SUM

def LTsd(a, b, d_prime, p):
    SUM = 0
    LocalSUM = 0
    for i in range(0, d_prime - 1):
        LocalSUM += LTs(a[i], b[i], p)
        LocalPRODUCT = 1
        for j in range(i + 1, d_prime - 1):
            LocalPRODUCT *= EQs(a[j], b[j], p)
        SUM += LocalSUM * LocalPRODUCT
    return SUM

def EQsd(a, b, d_prime, p):
    LocalPRODUCT = 1
    for i in range(0, d_prime):
        LocalPRODUCT *= EQs(a[i], b[i], p)
    return LocalPRODUCT

def EQs(a, b, p):
    val = ((a - b) ** (p - 1)) % p
    return (1- val)

def LTs(a, b, p):
    val_1 = (p+1)/2 * ((a - b)^(p-1))
    val_2 = 0
    for i in range(1, p-2):
        if i%2 == 1:
            val_2 += c_i(i, p) * (a - b)^i
    return (val_1 + val_2)

def c_i(i, p):
    SUM = 0
    for a in range(1, round((p-1)/2)):
        SUM += a^(p-1-i)
    return SUM
