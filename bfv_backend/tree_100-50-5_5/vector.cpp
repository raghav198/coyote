
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(5);
    ts[0] = encrypt_input("111110", info);
    ts[1] = encrypt_input("111111", info);
    ts[2] = encrypt_input("111110", info);
    ts[3] = encrypt_input("0111", info);
    ts[4] = encrypt_input("0111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[1];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->multiply(vs[0], ts[2], vs[1]); // __v1 = __v0 * __t2
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->multiply(vs[1], ts[3], vs[2]); // __v2 = __v1 * __t3
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->multiply(vs[2], ts[4], vs[3]); // __v3 = __v2 * __t4
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -1, gk, ss[0]); // __s0 = __v3 >> 1
    info.eval->multiply(ss[0], vs[1], vs[4]); // __v4 = __s0 * __v1
    info.eval->relinearize_inplace(vs[4], rk);
    return vs[4];
}
    