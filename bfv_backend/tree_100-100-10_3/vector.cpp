
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000000100", info);
    add_bitstring(bits, "0000010000000", info);
    add_bitstring(bits, "0000000100000", info);
    add_bitstring(bits, "0001000100000", info);
    add_bitstring(bits, "0000001000000", info);
    add_bitstring(bits, "0000000100001", info);
    add_bitstring(bits, "0000010000001", info);
    add_bitstring(bits, "0000000010000", info);
    add_bitstring(bits, "0001000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(18);
    ts[0] = encrypt_input("0001110001111101110111", info);
    ts[1] = encrypt_input("00010010001111110110111", info);
    ts[2] = encrypt_input("110101111101111101110010101110", info);
    ts[3] = encrypt_input("11111111011110111110011101110", info);
    ts[4] = encrypt_input("000000011000000", info);
    ts[7] = encrypt_input("00011100011100000", info);
    ts[11] = encrypt_input("00000000001100", info);
    ts[13] = encrypt_input("000000111000000", info);
    ts[15] = encrypt_input("000000111000000", info);
    ts[16] = encrypt_input("000000000011100", info);
    ts[17] = encrypt_input("000000000011100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[14];
    ctxt ss[6];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -7, gk, ss[1]); // __s1 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    
    // __t5 = blend(__s2@0000010000001, __v0@0000000010000, __t4@0000000100000)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[2], bits["0000010000001"], t5_1);
    info.eval->multiply_plain(vs[0], bits["0000000010000"], t5_2);
    info.eval->add_many({t5_1, t5_2, ts[4]}, ts[5]);
    
    
    // __t6 = blend(__v1@0000010000000, __v0@0000000100001, __s1@0000000010000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[1], bits["0000010000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["0000000100001"], t6_2);
    info.eval->multiply_plain(ss[1], bits["0000000010000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    info.eval->multiply(ts[5], ts[6], vs[2]); // __v2 = __t5 * __t6
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -11, gk, ss[3]); // __s3 = __v2 >> 11
    
    // __t8 = blend(__s2@0001000000000, __v2@0000000100000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[2], bits["0001000000000"], t8_1);
    info.eval->multiply_plain(vs[2], bits["0000000100000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    info.eval->add(ts[8], ts[7], vs[3]); // __v3 = __t8 + __t7
    
    // __t9 = blend(__v3@0001000100000, __s3@0000001000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["0001000100000"], t9_1);
    info.eval->multiply_plain(ss[3], bits["0000001000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    
    // __t10 = blend(__s3@0001000000000, __v1@0000001000000, __s1@0000000100000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[3], bits["0001000000000"], t10_1);
    info.eval->multiply_plain(vs[1], bits["0000001000000"], t10_2);
    info.eval->multiply_plain(ss[1], bits["0000000100000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[4]); // __v4 = __t9 * __t10
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -3, gk, ss[4]); // __s4 = __v4 >> 3
    
    // __t12 = blend(__v4@0000001000000, __t11@0000000000100)
    ctxt t12_1;
    info.eval->multiply_plain(vs[4], bits["0000001000000"], t12_1);
    info.eval->add(t12_1, ts[11], ts[12]);
    
    info.eval->multiply(ts[12], ss[4], vs[5]); // __v5 = __t12 * __s4
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t14 = blend(__s3@0000000000100, __t13@0000001000000)
    ctxt t14_1;
    info.eval->multiply_plain(ss[3], bits["0000000000100"], t14_1);
    info.eval->add(t14_1, ts[13], ts[14]);
    
    info.eval->add(vs[5], ts[14], vs[6]); // __v6 = __v5 + __t14
    info.eval->multiply(vs[6], ts[15], vs[7]); // __v7 = __v6 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -4, gk, ss[5]); // __s5 = __v7 >> 4
    info.eval->add(vs[6], ts[16], vs[8]); // __v8 = __v6 + __t16
    info.eval->multiply(ss[0], ss[5], vs[9]); // __v9 = __s0 * __s5
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->add(ss[2], vs[9], vs[10]); // __v10 = __s2 + __v9
    info.eval->add(ts[17], vs[8], vs[11]); // __v11 = __t17 + __v8
    info.eval->multiply(vs[11], vs[10], vs[12]); // __v12 = __v11 * __v10
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->multiply(vs[12], vs[0], vs[13]); // __v13 = __v12 * __v0
    info.eval->relinearize_inplace(vs[13], rk);
    return vs[13];
}
    