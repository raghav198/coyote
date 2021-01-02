import z3

value = z3.Datatype('value')
for i in range(10):
    value.declare(f'r{i}')

for let in 'bcdefghijklmn':
    value.declare(let)

value.declare('zero')
value.declare('one')
value.declare('X')


def is_register(val):
    return z3.Or(val == v.r0, val == v.r1, val == v.r2, val == v.r3, val == v.r4, val == v.r5, val == v.r6, val == v.r7, val == v.r8, val == v.r9)


targets = []
lefts = []
rights = []

v = value.create()

# b + c * (d + e); (f * g) + h + (i + j); (k + l) * (m + n)

add_eqns = [
    (v.r8, v.m, v.n),
    (v.r4, v.r3, v.h),
    (v.r7, v.k, v.l),
    (v.r0, v.d, v.e),
    (v.r5, v.i, v.j),
    (v.r2, v.b, v.r1),
    (v.r6, v.r4, v.r5),
    (v.X, v.X, v.X)
]

mul_eqns = [
    (v.r3, v.f, v.g),
    (v.r9, v.r7, v.r8),
    (v.r1, v.c, v.r0),
    (v.X, v.X, v.X)
]

adds = [1, 2, 4]
muls = [0, 3]

for slot in range(5):
    t = []
    l = []
    r = []
    for lane in range(3):
        t.append(z3.Const(f'target_{slot}_{lane}', v))
        l.append(z3.Const(f'left_{slot}_{lane}', v))
        r.append(z3.Const(f'right_{slot}_{lane}', v))
    targets.append(t)
    lefts.append(l)
    rights.append(r)

solver = z3.Optimize()


for i in adds:
    # impose the additive equation constraints
    for lane in range(3):
        eqn_constraints = []
        for x, y, z in add_eqns:
            eqn_constraints.append(z3.And(targets[i][lane] == x, (z3.Or(z3.And(lefts[i][lane] == y, rights[i][lane] == z),
                                                                        z3.And(lefts[i][lane] == z, rights[i][lane] == y)))))
        # free_t = z3.Const('free_t', v)
        # free_constraint = z3.ForAll([free_t], z3.Implies(targets[i][lane] == free_t, z3.Or(z3.And(lefts[i][lane] == v.zero, rights[i]
        #                                                                                           [lane] == free_t), z3.And(lefts[i][lane] == free_t, rights[i][lane] == v.zero))))
        free_constraint = z3.And(z3.Or(
            z3.And(targets[i][lane] == lefts[i]
                   [lane], rights[i][lane] == v.zero),
            z3.And(targets[i][lane] == rights[i][lane], lefts[i][lane] == v.zero)), z3.Not(is_register(targets[i][lane])))

        solver.add(
            z3.Or(free_constraint, z3.Or(*eqn_constraints)))

for i in muls:
    # impose multiplicative equation constraints
    for lane in range(3):
        eqn_constraints = []
        for x, y, z in mul_eqns:
            eqn_constraints.append(z3.And(targets[i][lane] == x, (z3.Or(z3.And(lefts[i][lane] == y, rights[i][lane] == z),
                                                                        z3.And(lefts[i][lane] == z, rights[i][lane] == y)))))
        # free_constraint = z3.ForAll([free_t], z3.Implies(targets[i][lane] == free_t, z3.Or(z3.And(lefts[i][lane] == v.one, rights[i]
        #                                                                                           [lane] == free_t), z3.And(lefts[i][lane] == free_t, rights[i][lane] == v.one))))

        free_constraint = z3.And(z3.Or(
            z3.And(targets[i][lane] == lefts[i]
                   [lane], rights[i][lane] == v.one),
            z3.And(targets[i][lane] == rights[i][lane], lefts[i][lane] == v.one)), z3.Not(is_register(targets[i][lane])))

        solver.add(
            z3.Or(free_constraint, z3.Or(*eqn_constraints)))

# now fill in the values we already have
solver.add(z3.And(targets[0][2] == v.r3,
                  lefts[0][2] == v.f, rights[0][2] == v.g))
solver.add(z3.And(targets[1][0] == v.r8,
                  lefts[1][0] == v.m, rights[1][0] == v.n))
solver.add(z3.And(targets[1][2] == v.r4,
                  lefts[1][2] == v.r3, rights[1][2] == v.h))
solver.add(z3.And(targets[2][0] == v.r7,
                  lefts[2][0] == v.k, rights[2][0] == v.l))
solver.add(z3.And(targets[2][1] == v.r0,
                  lefts[2][1] == v.d, rights[2][1] == v.e))
solver.add(z3.And(targets[2][2] == v.r5,
                  lefts[2][2] == v.i, rights[2][2] == v.j))
solver.add(z3.And(targets[3][0] == v.r9,
                  lefts[3][0] == v.r7, rights[3][0] == v.r8))
solver.add(z3.And(targets[3][1] == v.r1,
                  lefts[3][1] == v.c, rights[3][1] == v.r0))
solver.add(z3.And(targets[4][1] == v.r2,
                  lefts[4][1] == v.b, rights[4][1] == v.r1))
solver.add(z3.And(targets[4][2] == v.r6,
                  lefts[4][2] == v.r4, rights[4][2] == v.r5))

blends = []
for slot in range(5):
    for usages in range(slot + 1, 5):
        print(slot, usages)
        l_matches = [targets[slot][i] == lefts[usages][i]
                     for i in range(3)]
        r_matches = [targets[slot][i] == rights[usages][i]
                     for i in range(3)]
        blends.append(z3.And(
            z3.Or(*l_matches), z3.Not(z3.And(*l_matches))))
        blends.append(z3.And(
            z3.Or(*r_matches), z3.Not(z3.And(*r_matches))))


# blends = []
# for usage in range(1, 5):
#     lbest, rbest = 4, 4
#     for target in range(usage):
#         ldiff = z3.Sum([z3.If(
#             z3.And(targets[target][i] != lefts[usage][i], is_register(lefts[usage][i])), 1, 0) for i in range(3)])
#         rdiff = z3.Sum([z3.If(
#             z3.And(targets[target][i] != rights[usage][i], is_register(rights[usage][i])), 1, 0) for i in range(3)])
#         lbest = z3.If(ldiff < lbest, ldiff, lbest)
#         rbest = z3.If(rdiff < rbest, rdiff, rbest)
#     blends += [lbest, rbest]


solver.minimize(z3.Sum([z3.If(b, 1, 0) for b in blends]))

print(solver.check())

model = solver.model()

for slot in range(5):
    for vec in [targets, lefts, rights]:
        for lane in range(3):
            print(model[vec[slot][lane]], end='\t')
        print(';;', end='\t')
    print()

print([model.eval(b) for b in blends])
# print([model[b] for b in blends_vec])
