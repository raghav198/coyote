
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("111", info);
    ts[1] = encrypt_input("111", info);
    ts[2] = encrypt_input("111", info);
    ts[3] = encrypt_input("111", info);
    ts[4] = encrypt_input("111", info);
    ts[5] = encrypt_input("11", info);
    ts[6] = encrypt_input("111", info);
    ts[7] = encrypt_input("111", info);
    ts[8] = encrypt_input("111", info);
    ts[9] = encrypt_input("111", info);
    ts[10] = encrypt_input("111", info);
    ts[11] = encrypt_input("110", info);
    ts[12] = encrypt_input("111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[0];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->add(vs[1], vs[0], vs[2]); // __v2 = __v1 + __v0
    info.eval->add(ts[4], ts[5], vs[3]); // __v3 = __t4 + __t5
    info.eval->add(ts[6], vs[3], vs[4]); // __v4 = __t6 + __v3
    info.eval->add(ts[7], ts[8], vs[5]); // __v5 = __t7 + __t8
    info.eval->add(ts[9], vs[5], vs[6]); // __v6 = __t9 + __v5
    info.eval->multiply(vs[6], vs[4], vs[7]); // __v7 = __v6 * __v4
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->add(ts[10], vs[7], vs[8]); // __v8 = __t10 + __v7
    info.eval->add(ts[11], vs[2], vs[9]); // __v9 = __t11 + __v2
    info.eval->multiply(vs[9], ts[12], vs[10]); // __v10 = __v9 * __t12
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->add(vs[8], vs[10], vs[11]); // __v11 = __v8 + __v10
    return vs[11];
}
    