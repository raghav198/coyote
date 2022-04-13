
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10", info);
    add_bitstring(bits, "01", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(19);
    ts[0] = encrypt_input("111110", info);
    ts[1] = encrypt_input("111111", info);
    ts[2] = encrypt_input("110111", info);
    ts[3] = encrypt_input("110111", info);
    ts[4] = encrypt_input("1110", info);
    ts[6] = encrypt_input("1110", info);
    ts[7] = encrypt_input("0110", info);
    ts[10] = encrypt_input("1110", info);
    ts[11] = encrypt_input("110", info);
    ts[12] = encrypt_input("1110", info);
    ts[13] = encrypt_input("1111011", info);
    ts[15] = encrypt_input("1110", info);
    ts[16] = encrypt_input("1110", info);
    ts[17] = encrypt_input("1000", info);
    ts[18] = encrypt_input("111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[14];
    ctxt ss[1];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], vs[0], vs[1]); // __v1 = __t2 * __v0
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t5 = blend(__v1@01, __t4@10)
    ctxt t5_1;
    info.eval->multiply_plain(vs[1], bits["01"], t5_1);
    info.eval->add(t5_1, ts[4], ts[5]);
    
    info.eval->multiply(ts[3], ts[5], vs[2]); // __v2 = __t3 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t8 = blend(__v2@01, __t6@10)
    ctxt t8_1;
    info.eval->multiply_plain(vs[2], bits["01"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    
    // __t9 = blend(__v2@10, __t7@01)
    ctxt t9_1;
    info.eval->multiply_plain(vs[2], bits["10"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[3], ts[10], vs[4]); // __v4 = __v3 + __t10
    info.eval->add(vs[4], ts[11], vs[5]); // __v5 = __v4 + __t11
    info.eval->add(vs[1], vs[5], vs[6]); // __v6 = __v1 + __v5
    
    // __t14 = blend(__v3@01, __t12@10)
    ctxt t14_1;
    info.eval->multiply_plain(vs[3], bits["01"], t14_1);
    info.eval->add(t14_1, ts[12], ts[14]);
    
    info.eval->multiply(ts[14], ts[13], vs[7]); // __v7 = __t14 * __t13
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->add(vs[6], ts[15], vs[8]); // __v8 = __v6 + __t15
    info.eval->add(vs[8], ts[16], vs[9]); // __v9 = __v8 + __t16
    info.eval->add(vs[9], ts[17], vs[10]); // __v10 = __v9 + __t17
    info.eval->multiply(vs[7], ts[18], vs[11]); // __v11 = __v7 * __t18
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->multiply(vs[11], vs[10], vs[12]); // __v12 = __v11 * __v10
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -1, gk, ss[0]); // __s0 = __v12 >> 1
    info.eval->multiply(ss[0], vs[11], vs[13]); // __v13 = __s0 * __v11
    info.eval->relinearize_inplace(vs[13], rk);
    return vs[13];
}
    