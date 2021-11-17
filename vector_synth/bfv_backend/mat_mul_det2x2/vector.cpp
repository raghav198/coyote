
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(3);
    ts[0] = encrypt_input("1101111111110101111011111110111111011010", info);
    ts[2] = encrypt_input("1111111110110111101011111111101101111010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->multiply(vs[0], vs[1], vs[2]); // __v2 = __v0 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -3, gk, ss[0]); // __s0 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -2, gk, ss[1]); // __s1 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -1, gk, ss[2]); // __s2 = __v2 >> 1
    info.eval->add(ss[2], ss[0], vs[3]); // __v3 = __s2 + __s0
    info.eval->add(vs[2], ss[1], vs[4]); // __v4 = __v2 + __s1
    info.eval->multiply(vs[4], vs[3], vs[5]); // __v5 = __v4 * __v3
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -4, gk, ss[3]); // __s3 = __v5 >> 4
    info.eval->add(vs[5], ss[3], vs[6]); // __v6 = __v5 + __s3
    return vs[6];
}
    