
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000", info);
    add_bitstring(bits, "0010", info);
    add_bitstring(bits, "0110", info);
    add_bitstring(bits, "0001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(21);
    ts[0] = encrypt_input("111111111110", info);
    ts[1] = encrypt_input("1111111111", info);
    ts[2] = encrypt_input("01011110", info);
    ts[3] = encrypt_input("111000", info);
    ts[6] = encrypt_input("001100", info);
    ts[7] = encrypt_input("000111", info);
    ts[10] = encrypt_input("001110", info);
    ts[11] = encrypt_input("001010", info);
    ts[12] = encrypt_input("001110", info);
    ts[13] = encrypt_input("0001000", info);
    ts[14] = encrypt_input("001110", info);
    ts[17] = encrypt_input("000101", info);
    ts[18] = encrypt_input("000111", info);
    ts[19] = encrypt_input("000111", info);
    ts[20] = encrypt_input("000111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[14];
    ctxt ss[2];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    
    // __t4 = blend(__v0@1000, __t2@0110)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["1000"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    
    // __t5 = blend(__v0@0110, __t3@1000)
    ctxt t5_1;
    info.eval->multiply_plain(vs[0], bits["0110"], t5_1);
    info.eval->add(t5_1, ts[3], ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[1]); // __v1 = __t4 + __t5
    info.eval->rotate_rows(vs[1], -2, gk, ss[0]); // __s0 = __v1 >> 2
    
    // __t8 = blend(__s0@0001, __t6@0010)
    ctxt t8_1;
    info.eval->multiply_plain(ss[0], bits["0001"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    
    // __t9 = blend(__v1@0010, __t7@0001)
    ctxt t9_1;
    info.eval->multiply_plain(vs[1], bits["0010"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[2]); // __v2 = __t8 * __t9
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->add(ts[10], vs[2], vs[3]); // __v3 = __t10 + __v2
    info.eval->add(ts[11], ss[0], vs[4]); // __v4 = __t11 + __s0
    info.eval->add(vs[4], ts[12], vs[5]); // __v5 = __v4 + __t12
    info.eval->add(vs[3], vs[5], vs[6]); // __v6 = __v3 + __v5
    
    // __t15 = blend(__v6@0010, __t13@0001)
    ctxt t15_1;
    info.eval->multiply_plain(vs[6], bits["0010"], t15_1);
    info.eval->add(t15_1, ts[13], ts[15]);
    
    
    // __t16 = blend(__v2@0001, __t14@0010)
    ctxt t16_1;
    info.eval->multiply_plain(vs[2], bits["0001"], t16_1);
    info.eval->add(t16_1, ts[14], ts[16]);
    
    info.eval->multiply(ts[15], ts[16], vs[7]); // __v7 = __t15 * __t16
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -1, gk, ss[1]); // __s1 = __v7 >> 1
    info.eval->add(vs[0], vs[7], vs[8]); // __v8 = __v0 + __v7
    info.eval->add(ts[17], vs[8], vs[9]); // __v9 = __t17 + __v8
    info.eval->multiply(ss[1], ts[18], vs[10]); // __v10 = __s1 * __t18
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->multiply(ts[19], vs[10], vs[11]); // __v11 = __t19 * __v10
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->multiply(vs[11], ts[20], vs[12]); // __v12 = __v11 * __t20
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->add(vs[9], vs[12], vs[13]); // __v13 = __v9 + __v12
    return vs[13];
}
    