
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("101111", info);
    ts[1] = encrypt_input("111111", info);
    ts[2] = encrypt_input("1010", info);
    ts[3] = encrypt_input("1010", info);
    ts[4] = encrypt_input("1100", info);
    ts[5] = encrypt_input("1010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[1];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->add(ts[2], vs[0], vs[1]); // __v1 = __t2 + __v0
    info.eval->multiply(ss[0], vs[1], vs[2]); // __v2 = __s0 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(ts[3], ts[4], vs[3]); // __v3 = __t3 + __t4
    info.eval->add(ts[5], vs[2], vs[4]); // __v4 = __t5 + __v2
    info.eval->add(vs[4], vs[3], vs[5]); // __v5 = __v4 + __v3
    return vs[5];
}
    