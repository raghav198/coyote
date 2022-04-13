
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000000", info);
    add_bitstring(bits, "0010000", info);
    add_bitstring(bits, "0101000", info);
    add_bitstring(bits, "0000100", info);
    add_bitstring(bits, "0001000", info);
    add_bitstring(bits, "0000001", info);
    add_bitstring(bits, "0000010", info);
    add_bitstring(bits, "0100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(27);
    ts[0] = encrypt_input("111011101111110", info);
    ts[1] = encrypt_input("111011101101110", info);
    ts[2] = encrypt_input("01110101100101", info);
    ts[3] = encrypt_input("0111011100101", info);
    ts[4] = encrypt_input("111111011101110", info);
    ts[5] = encrypt_input("111000000", info);
    ts[7] = encrypt_input("001110000", info);
    ts[8] = encrypt_input("000001110", info);
    ts[11] = encrypt_input("000011100", info);
    ts[12] = encrypt_input("000010100", info);
    ts[15] = encrypt_input("000111000", info);
    ts[16] = encrypt_input("000011100", info);
    ts[19] = encrypt_input("000111000", info);
    ts[22] = encrypt_input("000000111", info);
    ts[25] = encrypt_input("000000111", info);
    ts[26] = encrypt_input("000000111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[14];
    ctxt ss[5];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    
    // __t6 = blend(__v1@0101000, __v0@0000010, __t5@1000000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[1], bits["0101000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["0000010"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[5]}, ts[6]);
    
    info.eval->add(ts[4], ts[6], vs[2]); // __v2 = __t4 + __t6
    info.eval->rotate_rows(vs[2], -1, gk, ss[0]); // __s0 = __v2 >> 1
    
    // __t9 = blend(__v0@1000000, __v2@0000010, __t7@0010000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[0], bits["1000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["0000010"], t9_2);
    info.eval->add_many({t9_1, t9_2, ts[7]}, ts[9]);
    
    
    // __t10 = blend(__v2@1000000, __v0@0010000, __t8@0000010)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[2], bits["1000000"], t10_1);
    info.eval->multiply_plain(vs[0], bits["0010000"], t10_2);
    info.eval->add_many({t10_1, t10_2, ts[8]}, ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[3]); // __v3 = __t9 * __t10
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -1, gk, ss[1]); // __s1 = __v3 >> 1
    
    // __t13 = blend(__s1@0100000, __t11@0000100)
    ctxt t13_1;
    info.eval->multiply_plain(ss[1], bits["0100000"], t13_1);
    info.eval->add(t13_1, ts[11], ts[13]);
    
    
    // __t14 = blend(__v2@0100000, __t12@0000100)
    ctxt t14_1;
    info.eval->multiply_plain(vs[2], bits["0100000"], t14_1);
    info.eval->add(t14_1, ts[12], ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[4]); // __v4 = __t13 * __t14
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -3, gk, ss[2]); // __s2 = __v4 >> 3
    
    // __t17 = blend(__v4@0000100, __t15@0001000)
    ctxt t17_1;
    info.eval->multiply_plain(vs[4], bits["0000100"], t17_1);
    info.eval->add(t17_1, ts[15], ts[17]);
    
    
    // __t18 = blend(__s1@0001000, __t16@0000100)
    ctxt t18_1;
    info.eval->multiply_plain(ss[1], bits["0001000"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    info.eval->add(ts[17], ts[18], vs[5]); // __v5 = __t17 + __t18
    
    // __t20 = blend(__v5@0001000, __s0@0000100)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[5], bits["0001000"], t20_1);
    info.eval->multiply_plain(ss[0], bits["0000100"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v5@0000100, __t19@0001000)
    ctxt t21_1;
    info.eval->multiply_plain(vs[5], bits["0000100"], t21_1);
    info.eval->add(t21_1, ts[19], ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[6]); // __v6 = __t20 + __t21
    info.eval->rotate_rows(vs[6], -3, gk, ss[3]); // __s3 = __v6 >> 3
    
    // __t23 = blend(__s2@0000100, __s3@0000001)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(ss[2], bits["0000100"], t23_1);
    info.eval->multiply_plain(ss[3], bits["0000001"], t23_2);
    info.eval->add(t23_1, t23_2, ts[23]);
    
    
    // __t24 = blend(__v6@0000100, __t22@0000001)
    ctxt t24_1;
    info.eval->multiply_plain(vs[6], bits["0000100"], t24_1);
    info.eval->add(t24_1, ts[22], ts[24]);
    
    info.eval->add(ts[23], ts[24], vs[7]); // __v7 = __t23 + __t24
    info.eval->multiply(vs[0], vs[7], vs[8]); // __v8 = __v0 * __v7
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -2, gk, ss[4]); // __s4 = __v8 >> 2
    info.eval->multiply(vs[7], ss[4], vs[9]); // __v9 = __v7 * __s4
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->multiply(ss[1], vs[9], vs[10]); // __v10 = __s1 * __v9
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->multiply(vs[10], ts[25], vs[11]); // __v11 = __v10 * __t25
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->add(ts[26], vs[11], vs[12]); // __v12 = __t26 + __v11
    info.eval->add(vs[1], vs[12], vs[13]); // __v13 = __v1 + __v12
    return vs[13];
}
    