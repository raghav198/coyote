
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(11);
    ts[0] = encrypt_input("111", info);
    ts[1] = encrypt_input("111", info);
    ts[2] = encrypt_input("111", info);
    ts[3] = encrypt_input("111", info);
    ts[4] = encrypt_input("11", info);
    ts[5] = encrypt_input("101", info);
    ts[6] = encrypt_input("111", info);
    ts[7] = encrypt_input("111", info);
    ts[8] = encrypt_input("111", info);
    ts[9] = encrypt_input("111", info);
    ts[10] = encrypt_input("111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[0];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->multiply(vs[1], ts[4], vs[2]); // __v2 = __v1 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(ts[5], ts[6], vs[3]); // __v3 = __t5 + __t6
    info.eval->add(vs[0], vs[3], vs[4]); // __v4 = __v0 + __v3
    info.eval->add(vs[4], vs[2], vs[5]); // __v5 = __v4 + __v2
    info.eval->multiply(ts[7], ts[8], vs[6]); // __v6 = __t7 * __t8
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[5], vs[6], vs[7]); // __v7 = __v5 + __v6
    info.eval->add(ts[9], vs[7], vs[8]); // __v8 = __t9 + __v7
    info.eval->add(vs[8], ts[10], vs[9]); // __v9 = __v8 + __t10
    return vs[9];
}
    