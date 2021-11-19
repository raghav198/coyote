
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(7);
    ts[0] = encrypt_input("111111", info);
    ts[1] = encrypt_input("111111", info);
    ts[2] = encrypt_input("11111", info);
    ts[3] = encrypt_input("1100", info);
    ts[4] = encrypt_input("1110", info);
    ts[5] = encrypt_input("110", info);
    ts[6] = encrypt_input("1110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(vs[0], ts[2], vs[1]); // __v1 = __v0 * __t2
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -1, gk, ss[0]); // __s0 = __v1 >> 1
    info.eval->multiply(ts[3], ts[4], vs[2]); // __v2 = __t3 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(vs[1], ss[0], vs[3]); // __v3 = __v1 + __s0
    info.eval->add(vs[2], vs[3], vs[4]); // __v4 = __v2 + __v3
    info.eval->multiply(vs[4], ts[5], vs[5]); // __v5 = __v4 * __t5
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->multiply(ts[6], vs[5], vs[6]); // __v6 = __t6 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    