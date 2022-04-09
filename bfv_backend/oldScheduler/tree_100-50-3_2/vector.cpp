
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(4);
    ts[0] = encrypt_input("000111", info);
    ts[1] = encrypt_input("000111", info);
    ts[2] = encrypt_input("11110111110", info);
    ts[3] = encrypt_input("1101111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[3];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -2, gk, ss[1]); // __s1 = __v1 >> 2
    info.eval->add(vs[1], ss[0], vs[2]); // __v2 = __v1 + __s0
    info.eval->multiply(ss[1], vs[1], vs[3]); // __v3 = __s1 * __v1
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -1, gk, ss[2]); // __s2 = __v3 >> 1
    info.eval->multiply(ss[2], vs[2], vs[4]); // __v4 = __s2 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    return vs[4];
}
    