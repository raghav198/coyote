
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000001000000000010000000", info);
    add_bitstring(bits, "00000000010000000010000000000000", info);
    add_bitstring(bits, "01000000000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000001000", info);
    add_bitstring(bits, "00000000000000000000000001001000", info);
    add_bitstring(bits, "00000000000000100000000000000000", info);
    add_bitstring(bits, "00000000000000000001000000000000", info);
    add_bitstring(bits, "00001000000000000000000000000000", info);
    add_bitstring(bits, "00000100000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000010000", info);
    add_bitstring(bits, "00000000000010000000000000000000", info);
    add_bitstring(bits, "00000000000000000010000000000000", info);
    add_bitstring(bits, "00000000000010000000000001000000", info);
    add_bitstring(bits, "00000000000000010000000000000000", info);
    add_bitstring(bits, "00000000000000000100000000000000", info);
    add_bitstring(bits, "00000000010000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000010000000", info);
    add_bitstring(bits, "00000000000000001000000000000000", info);
    add_bitstring(bits, "00000000000001000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000000100", info);
    add_bitstring(bits, "10000000000000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(21);
    ts[0] = encrypt_input("1010000111000111011100111111011011011100000111011101110", info);
    ts[1] = encrypt_input("111000011100011011100111111011101101110000011011101110", info);
    ts[2] = encrypt_input("0110111111000111111000111111001110111001110111101111011001110111", info);
    ts[3] = encrypt_input("01101111110001111110001011111001110110011101011111111011101110110", info);
    ts[4] = encrypt_input("0000000001100000000011100100000001110000", info);
    ts[5] = encrypt_input("0000000001100000000011111100000001110000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[19];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -19, gk, ss[0]); // __s0 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -18, gk, ss[2]); // __s2 = __v0 >> 18
    info.eval->rotate_rows(vs[0], -29, gk, ss[3]); // __s3 = __v0 >> 29
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -3, gk, ss[4]); // __s4 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -29, gk, ss[5]); // __s5 = __v1 >> 29
    info.eval->rotate_rows(vs[1], -18, gk, ss[6]); // __s6 = __v1 >> 18
    
    // __t6 = blend(__s4@00000100000000000000000000000000, __s3@00000000000000001000000000000000, __v0@00000000000000000100000000000000, __v1@00000000000000000000000000000100, __t4@00000000010000000011000000010000)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[4], bits["00000100000000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[3], bits["00000000000000001000000000000000"], t6_2);
    info.eval->multiply_plain(vs[0], bits["00000000000000000100000000000000"], t6_3);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000000000000100"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__s5@00000100000000000000000000000000, __v1@00000000000000001000000000000000, __s3@00000000000000000100000000000000, __s1@00000000000000000000000000000100, __t5@00000000010000000011000000010000)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[5], bits["00000100000000000000000000000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["00000000000000001000000000000000"], t7_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000000100000000000000"], t7_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000000000000100"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, ts[5]}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -28, gk, ss[7]); // __s7 = __v2 >> 28
    info.eval->rotate_rows(vs[2], -1, gk, ss[8]); // __s8 = __v2 >> 1
    
    // __t8 = blend(__s5@10000000000000000000000000000000, __s6@00000000010000000000000000000000, __s1@00000000000010000000000000000000, __v1@00000000000000000010000000000000, __s4@00000000000000000000000000001000)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5;
    info.eval->multiply_plain(ss[5], bits["10000000000000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[6], bits["00000000010000000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[1], bits["00000000000010000000000000000000"], t8_3);
    info.eval->multiply_plain(vs[1], bits["00000000000000000010000000000000"], t8_4);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000000000001000"], t8_5);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5}, ts[8]);
    
    
    // __t9 = blend(__s2@10000000000000000000000000000000, __v2@00000000010000000010000000000000, __v1@00000000000010000000000000000000, __s5@00000000000000000000000000001000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[2], bits["10000000000000000000000000000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["00000000010000000010000000000000"], t9_2);
    info.eval->multiply_plain(vs[1], bits["00000000000010000000000000000000"], t9_3);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000000000001000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -1, gk, ss[9]); // __s9 = __v3 >> 1
    info.eval->rotate_rows(vs[3], -28, gk, ss[10]); // __s10 = __v3 >> 28
    
    // __t10 = blend(__s4@00001000000000000000000000000000, __v1@00000000000001000000000010000000, __s2@00000000000000100000000000000000, __s0@00000000000000000001000000000000, __v2@00000000000000000000000000010000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(ss[4], bits["00001000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[1], bits["00000000000001000000000010000000"], t10_2);
    info.eval->multiply_plain(ss[2], bits["00000000000000100000000000000000"], t10_3);
    info.eval->multiply_plain(ss[0], bits["00000000000000000001000000000000"], t10_4);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000000000010000"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__s5@00001000000000000000000000000000, __s6@00000000000001000000000000000000, __s1@00000000000000100000000000000000, __v2@00000000000000000001000000000000, __s0@00000000000000000000000010000000, __s3@00000000000000000000000000010000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6;
    info.eval->multiply_plain(ss[5], bits["00001000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[6], bits["00000000000001000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[1], bits["00000000000000100000000000000000"], t11_3);
    info.eval->multiply_plain(vs[2], bits["00000000000000000001000000000000"], t11_4);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000010000000"], t11_5);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000000000010000"], t11_6);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[4]); // __v4 = __t10 + __t11
    info.eval->rotate_rows(vs[4], -1, gk, ss[11]); // __s11 = __v4 >> 1
    info.eval->rotate_rows(vs[4], -28, gk, ss[12]); // __s12 = __v4 >> 28
    
    // __t12 = blend(__s7@00000000000010000000000001000000, __s11@00000000000000010000000000000000, __s1@00000000000000000010000000000000, __v3@00000000000000000000000000001000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[7], bits["00000000000010000000000001000000"], t12_1);
    info.eval->multiply_plain(ss[11], bits["00000000000000010000000000000000"], t12_2);
    info.eval->multiply_plain(ss[1], bits["00000000000000000010000000000000"], t12_3);
    info.eval->multiply_plain(vs[3], bits["00000000000000000000000000001000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__v3@00000000000010000000000000000000, __s12@00000000000000010000000000000000, __s5@00000000000000000010000000000000, __s11@00000000000000000000000001001000)
    ctxt t13_1, t13_2, t13_3, t13_4;
    info.eval->multiply_plain(vs[3], bits["00000000000010000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[12], bits["00000000000000010000000000000000"], t13_2);
    info.eval->multiply_plain(ss[5], bits["00000000000000000010000000000000"], t13_3);
    info.eval->multiply_plain(ss[11], bits["00000000000000000000000001001000"], t13_4);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[5]); // __v5 = __t12 * __t13
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -19, gk, ss[13]); // __s13 = __v5 >> 19
    info.eval->multiply(ss[8], vs[5], vs[6]); // __v6 = __s8 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -19, gk, ss[14]); // __s14 = __v6 >> 19
    
    // __t14 = blend(__s11@00000100000000000000000000000000, __s10@00000000000000100000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[11], bits["00000100000000000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000100000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__s10@00000100000000000000000000000000, __s11@00000000000000100000000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[10], bits["00000100000000000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[11], bits["00000000000000100000000000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[7]); // __v7 = __t14 + __t15
    info.eval->rotate_rows(vs[7], -19, gk, ss[15]); // __s15 = __v7 >> 19
    
    // __t16 = blend(__s7@01000000000000000000000000000000, __s13@00000000000010000000000000000000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(ss[7], bits["01000000000000000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[13], bits["00000000000010000000000000000000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__s9@01000000000000000000000000000000, __v5@00000000000010000000000000000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[9], bits["01000000000000000000000000000000"], t17_1);
    info.eval->multiply_plain(vs[5], bits["00000000000010000000000000000000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[8]); // __v8 = __t16 * __t17
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -7, gk, ss[16]); // __s16 = __v8 >> 7
    
    // __t18 = blend(__s15@01000000000000000000000000000000, __v7@00000100000000000000000000000000, __v5@00000000000000010000000000000000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(ss[15], bits["01000000000000000000000000000000"], t18_1);
    info.eval->multiply_plain(vs[7], bits["00000100000000000000000000000000"], t18_2);
    info.eval->multiply_plain(vs[5], bits["00000000000000010000000000000000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    
    // __t19 = blend(__v8@01000000000000000000000000000000, __s14@00000100000000000000000000000000, __s13@00000000000000010000000000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[8], bits["01000000000000000000000000000000"], t19_1);
    info.eval->multiply_plain(ss[14], bits["00000100000000000000000000000000"], t19_2);
    info.eval->multiply_plain(ss[13], bits["00000000000000010000000000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[9]); // __v9 = __t18 + __t19
    info.eval->rotate_rows(vs[9], -4, gk, ss[17]); // __s17 = __v9 >> 4
    
    // __t20 = blend(__v9@00000100000000000000000000000000, __s16@00000000000000000001000000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[9], bits["00000100000000000000000000000000"], t20_1);
    info.eval->multiply_plain(ss[16], bits["00000000000000000001000000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    info.eval->multiply(ss[17], ts[20], vs[10]); // __v10 = __s17 * __t20
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -18, gk, ss[18]); // __s18 = __v10 >> 18
    info.eval->multiply(ss[18], vs[10], vs[11]); // __v11 = __s18 * __v10
    info.eval->relinearize_inplace(vs[11], rk);
    return vs[11];
}
    