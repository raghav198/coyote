
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(4);
    ts[0] = encrypt_input("111111", info);
    ts[1] = encrypt_input("111111", info);
    ts[2] = encrypt_input("11011", info);
    ts[3] = encrypt_input("111101", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->add(vs[1], vs[0], vs[2]); // __v2 = __v1 + __v0
    info.eval->rotate_rows(vs[2], -1, gk, ss[0]); // __s0 = __v2 >> 1
    info.eval->multiply(vs[2], ss[0], vs[3]); // __v3 = __v2 * __s0
    info.eval->relinearize_inplace(vs[3], rk);
    return vs[3];
}
    