
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10000000000000110000000", info);
    add_bitstring(bits, "00000100000000001000000", info);
    add_bitstring(bits, "00000001000000000000000", info);
    add_bitstring(bits, "00000000000000000000100", info);
    add_bitstring(bits, "00000000000000000010000", info);
    add_bitstring(bits, "00100000000000000000000", info);
    add_bitstring(bits, "00000010000010000000100", info);
    add_bitstring(bits, "00010000010000000000000", info);
    add_bitstring(bits, "00000000010000000000000", info);
    add_bitstring(bits, "00001100001000000000000", info);
    add_bitstring(bits, "00000000000000010000000", info);
    add_bitstring(bits, "00000000000001000000000", info);
    add_bitstring(bits, "00010000000000000000000", info);
    add_bitstring(bits, "00001100000001000000000", info);
    add_bitstring(bits, "00000000001100000011000", info);
    add_bitstring(bits, "00000000000000001000000", info);
    add_bitstring(bits, "00000000100000010000000", info);
    add_bitstring(bits, "00010000000000001000000", info);
    add_bitstring(bits, "00000000010100000000000", info);
    add_bitstring(bits, "00000000010000000000100", info);
    add_bitstring(bits, "00000000000000100000000", info);
    add_bitstring(bits, "00000000100000001000000", info);
    add_bitstring(bits, "00000100000000000010000", info);
    add_bitstring(bits, "00001010000010000100100", info);
    add_bitstring(bits, "00010000100000000000000", info);
    add_bitstring(bits, "10000000000000000000000", info);
    add_bitstring(bits, "10010000011000000010000", info);
    add_bitstring(bits, "00000100000000000000000", info);
    add_bitstring(bits, "00000000000000000001000", info);
    add_bitstring(bits, "00000000000000000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(28);
    ts[0] = encrypt_input("01111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111110111111111111111111111111111100111111111111111111111111111100", info);
    ts[1] = encrypt_input("01111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111110111111111111111111111111111100111111111111111111111111111100", info);
    ts[2] = encrypt_input("10011111111010011110100", info);
    ts[4] = encrypt_input("01111111111111111111111111111111111111111111111111111111100011111111111111111111111111111111111111111111111111111111111111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111101111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[5] = encrypt_input("01111111111111111111111111111111111111111111111111111111100011111111111111111111111111111111111111111111111111111111111111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111101111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[17];
    ctxt ss[24];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -21, gk, ss[2]); // __s2 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -2, gk, ss[3]); // __s3 = __v0 >> 2
    
    // __t3 = blend(__s2@10010000011000000010000, __s1@00001010000010000100100, __s0@00000100000000001000000, __v0@00000001000000000000000, __s3@00000000100000010000000)
    ctxt t3_1, t3_2, t3_3, t3_4, t3_5;
    info.eval->multiply_plain(ss[2], bits["10010000011000000010000"], t3_1);
    info.eval->multiply_plain(ss[1], bits["00001010000010000100100"], t3_2);
    info.eval->multiply_plain(ss[0], bits["00000100000000001000000"], t3_3);
    info.eval->multiply_plain(vs[0], bits["00000001000000000000000"], t3_4);
    info.eval->multiply_plain(ss[3], bits["00000000100000010000000"], t3_5);
    info.eval->add_many({t3_1, t3_2, t3_3, t3_4, t3_5}, ts[3]);
    
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->rotate_rows(vs[1], -3, gk, ss[4]); // __s4 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -21, gk, ss[5]); // __s5 = __v1 >> 21
    info.eval->rotate_rows(vs[1], -20, gk, ss[6]); // __s6 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -1, gk, ss[7]); // __s7 = __v1 >> 1
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -3, gk, ss[8]); // __s8 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -21, gk, ss[9]); // __s9 = __v2 >> 21
    info.eval->rotate_rows(vs[2], -1, gk, ss[10]); // __s10 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -20, gk, ss[11]); // __s11 = __v2 >> 20
    
    // __t6 = blend(__s5@00001100001000000000000, __s1@00000010000010000000100, __s7@00000000010100000000000, __s0@00000000000001000000000, __s3@00000000000000000100000, __v1@00000000000000000010000, __s4@00000000000000000001000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7;
    info.eval->multiply_plain(ss[5], bits["00001100001000000000000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["00000010000010000000100"], t6_2);
    info.eval->multiply_plain(ss[7], bits["00000000010100000000000"], t6_3);
    info.eval->multiply_plain(ss[0], bits["00000000000001000000000"], t6_4);
    info.eval->multiply_plain(ss[3], bits["00000000000000000100000"], t6_5);
    info.eval->multiply_plain(vs[1], bits["00000000000000000010000"], t6_6);
    info.eval->multiply_plain(ss[4], bits["00000000000000000001000"], t6_7);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7}, ts[6]);
    
    
    // __t7 = blend(__s8@00001100000001000000000, __v2@00000010000010000000100, __s9@00000000010000000000000, __s11@00000000001100000011000, __s10@00000000000000000100000)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5;
    info.eval->multiply_plain(ss[8], bits["00001100000001000000000"], t7_1);
    info.eval->multiply_plain(vs[2], bits["00000010000010000000100"], t7_2);
    info.eval->multiply_plain(ss[9], bits["00000000010000000000000"], t7_3);
    info.eval->multiply_plain(ss[11], bits["00000000001100000011000"], t7_4);
    info.eval->multiply_plain(ss[10], bits["00000000000000000100000"], t7_5);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -19, gk, ss[12]); // __s12 = __v3 >> 19
    info.eval->rotate_rows(vs[3], -21, gk, ss[13]); // __s13 = __v3 >> 21
    info.eval->rotate_rows(vs[3], -17, gk, ss[14]); // __s14 = __v3 >> 17
    
    // __t8 = blend(__s2@00000100000000000010000, __s1@00000000010000000000000, __v1@00000000000000000000100)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[2], bits["00000100000000000010000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["00000000010000000000000"], t8_2);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000100"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s9@00000100000000000000000, __s10@00000000010000000000100, __v2@00000000000000000010000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[9], bits["00000100000000000000000"], t9_1);
    info.eval->multiply_plain(ss[10], bits["00000000010000000000100"], t9_2);
    info.eval->multiply_plain(vs[2], bits["00000000000000000010000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -21, gk, ss[15]); // __s15 = __v4 >> 21
    info.eval->rotate_rows(vs[4], -19, gk, ss[16]); // __s16 = __v4 >> 19
    
    // __t10 = blend(__s14@10000000000000000000000, __s15@00010000000000000000000, __s12@00000000100000001000000, __v4@00000000010000000000000, __s16@00000000000000100000000, __s13@00000000000000010000000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6;
    info.eval->multiply_plain(ss[14], bits["10000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[15], bits["00010000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[12], bits["00000000100000001000000"], t10_3);
    info.eval->multiply_plain(vs[4], bits["00000000010000000000000"], t10_4);
    info.eval->multiply_plain(ss[16], bits["00000000000000100000000"], t10_5);
    info.eval->multiply_plain(ss[13], bits["00000000000000010000000"], t10_6);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6}, ts[10]);
    
    
    // __t11 = blend(__s12@10000000000000110000000, __s13@00010000100000000000000, __v3@00000000010000000000000, __s16@00000000000000001000000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[12], bits["10000000000000110000000"], t11_1);
    info.eval->multiply_plain(ss[13], bits["00010000100000000000000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["00000000010000000000000"], t11_3);
    info.eval->multiply_plain(ss[16], bits["00000000000000001000000"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    info.eval->rotate_rows(vs[5], -2, gk, ss[17]); // __s17 = __v5 >> 2
    info.eval->rotate_rows(vs[5], -17, gk, ss[18]); // __s18 = __v5 >> 17
    
    // __t12 = blend(__s5@00100000000000000000000, __s2@00010000000000000000000, __v1@00000000010000000000000, __s1@00000000000000001000000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[5], bits["00100000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[2], bits["00010000000000000000000"], t12_2);
    info.eval->multiply_plain(vs[1], bits["00000000010000000000000"], t12_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000001000000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__s17@00100000000000000000000, __s18@00010000010000000000000, __v5@00000000000000001000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[17], bits["00100000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[18], bits["00010000010000000000000"], t13_2);
    info.eval->multiply_plain(vs[5], bits["00000000000000001000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__s0@00100000000000000000000, __s7@00000000000000001000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[0], bits["00100000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000001000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__s18@00100000000000000000000, __s17@00000000000000001000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[18], bits["00100000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[17], bits["00000000000000001000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t16 = blend(__v7@00100000000000000000000, __s12@00000000010000000000000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(vs[7], bits["00100000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[12], bits["00000000010000000000000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__v6@00100000000000000000000, __s13@00000000010000000000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[6], bits["00100000000000000000000"], t17_1);
    info.eval->multiply_plain(ss[13], bits["00000000010000000000000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[8]); // __v8 = __t16 + __t17
    
    // __t18 = blend(__v1@00010000000000000000000, __s2@00000000010000000000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[1], bits["00010000000000000000000"], t18_1);
    info.eval->multiply_plain(ss[2], bits["00000000010000000000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    
    // __t19 = blend(__v5@00010000000000000000000, __v8@00000000010000000000000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[5], bits["00010000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[8], bits["00000000010000000000000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[9]); // __v9 = __t18 * __t19
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t20 = blend(__v6@00010000000000001000000, __v9@00000000010000000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[6], bits["00010000000000001000000"], t20_1);
    info.eval->multiply_plain(vs[9], bits["00000000010000000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v9@00010000000000000000000, __v6@00000000010000000000000, __v7@00000000000000001000000)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(vs[9], bits["00010000000000000000000"], t21_1);
    info.eval->multiply_plain(vs[6], bits["00000000010000000000000"], t21_2);
    info.eval->multiply_plain(vs[7], bits["00000000000000001000000"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[10]); // __v10 = __t20 + __t21
    info.eval->rotate_rows(vs[10], -16, gk, ss[19]); // __s19 = __v10 >> 16
    info.eval->rotate_rows(vs[10], -10, gk, ss[20]); // __s20 = __v10 >> 10
    
    // __t22 = blend(__s2@00100000000000000000000, __s4@00010000000000000000000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(ss[2], bits["00100000000000000000000"], t22_1);
    info.eval->multiply_plain(ss[4], bits["00010000000000000000000"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);
    
    
    // __t23 = blend(__s19@00100000000000000000000, __s20@00010000000000000000000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(ss[19], bits["00100000000000000000000"], t23_1);
    info.eval->multiply_plain(ss[20], bits["00010000000000000000000"], t23_2);
    info.eval->add(t23_1, t23_2, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[11]); // __v11 = __t22 * __t23
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -12, gk, ss[21]); // __s21 = __v11 >> 12
    
    // __t24 = blend(__s6@00100000000000000000000, __s0@00010000000000000000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(ss[6], bits["00100000000000000000000"], t24_1);
    info.eval->multiply_plain(ss[0], bits["00010000000000000000000"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    
    // __t25 = blend(__v8@00100000000000000000000, __v10@00010000000000000000000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(vs[8], bits["00100000000000000000000"], t25_1);
    info.eval->multiply_plain(vs[10], bits["00010000000000000000000"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[12]); // __v12 = __t24 * __t25
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -12, gk, ss[22]); // __s22 = __v12 >> 12
    
    // __t26 = blend(__s21@00000000000000100000000, __s22@00000000000000010000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(ss[21], bits["00000000000000100000000"], t26_1);
    info.eval->multiply_plain(ss[22], bits["00000000000000010000000"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__s22@00000000000000100000000, __s21@00000000000000010000000)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(ss[22], bits["00000000000000100000000"], t27_1);
    info.eval->multiply_plain(ss[21], bits["00000000000000010000000"], t27_2);
    info.eval->add(t27_1, t27_2, ts[27]);
    
    info.eval->add(ts[26], ts[27], vs[13]); // __v13 = __t26 + __t27
    info.eval->rotate_rows(vs[13], -22, gk, ss[23]); // __s23 = __v13 >> 22
    info.eval->multiply(ss[6], vs[13], vs[14]); // __v14 = __s6 * __v13
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->multiply(vs[0], ss[23], vs[15]); // __v15 = __v0 * __s23
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->add(vs[15], vs[14], vs[16]); // __v16 = __v15 + __v14
    return vs[16];
}
    