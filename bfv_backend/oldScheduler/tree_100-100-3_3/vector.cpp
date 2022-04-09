
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(2);
    ts[0] = encrypt_input("111111111110", info);
    ts[1] = encrypt_input("11110101111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[3];
    ctxt ss[2];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->multiply(ss[0], vs[0], vs[1]); // __v1 = __s0 * __v0
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -3, gk, ss[1]); // __s1 = __v1 >> 3
    info.eval->multiply(ss[1], vs[1], vs[2]); // __v2 = __s1 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    return vs[2];
}
    