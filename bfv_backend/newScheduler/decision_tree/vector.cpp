
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("101", info);
    ts[1] = encrypt_input("1111111111111111110111111111111111111", info);
    ts[2] = encrypt_input("111111111111111111101111111111111111111", info);
    ts[3] = encrypt_input("1111111111111111110111111111111111111", info);
    ts[4] = encrypt_input("111111111111111111101111111111111111111", info);
    ts[5] = encrypt_input("101", info);
    ts[6] = encrypt_input("1111111111111111110111111111111111111", info);
    ts[7] = encrypt_input("1111111111111111110111111111111111111", info);
    ts[8] = encrypt_input("111111111111111111101111111111111111111", info);
    ts[9] = encrypt_input("100", info);
    ts[10] = encrypt_input("11111111111111111100", info);
    ts[11] = encrypt_input("00111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(vs[0], ts[2], vs[1]); // __v1 = __v0 * __t2
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->multiply(ts[3], ts[4], vs[2]); // __v2 = __t3 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(vs[2], vs[1], vs[3]); // __v3 = __v2 + __v1
    info.eval->add(ts[5], ts[6], vs[4]); // __v4 = __t5 + __t6
    info.eval->multiply(vs[4], vs[3], vs[5]); // __v5 = __v4 * __v3
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->multiply(ts[7], ts[8], vs[6]); // __v6 = __t7 * __t8
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[6], vs[5], vs[7]); // __v7 = __v6 + __v5
    info.eval->add(ts[9], ts[10], vs[8]); // __v8 = __t9 + __t10
    
    // __t12 = blend(__v8@100, __t11@001)
    ctxt t12_1;
    info.eval->multiply_plain(vs[8], bits["100"], t12_1);
    info.eval->add(t12_1, ts[11], ts[12]);
    
    info.eval->multiply(ts[12], vs[7], vs[9]); // __v9 = __t12 * __v7
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -1, gk, ss[0]); // __s0 = __v9 >> 1
    info.eval->add(ss[0], vs[9], vs[10]); // __v10 = __s0 + __v9
    return vs[10];
}
    