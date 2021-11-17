
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00010000000000000000000000", info);
    add_bitstring(bits, "00000000000000000001000000", info);
    add_bitstring(bits, "00000000000000000000011000", info);
    add_bitstring(bits, "00000000000000000000000100", info);
    add_bitstring(bits, "00000000000000000000000001", info);
    add_bitstring(bits, "00000000000000010000000000", info);
    add_bitstring(bits, "00000000000000000100000000", info);
    add_bitstring(bits, "00000000000000000000101000", info);
    add_bitstring(bits, "10000000000000000000000000", info);
    add_bitstring(bits, "00000000000010000000000000", info);
    add_bitstring(bits, "00000001000000000000000000", info);
    add_bitstring(bits, "00000000000000001000000000", info);
    add_bitstring(bits, "00000100000000000000000010", info);
    add_bitstring(bits, "00000000000000000000001000", info);
    add_bitstring(bits, "00000000000000000000000010", info);
    add_bitstring(bits, "00000001010000000000000000", info);
    add_bitstring(bits, "00000000010000000000000000", info);
    add_bitstring(bits, "01000000000000000000000000", info);
    add_bitstring(bits, "00000000000100000000000000", info);
    add_bitstring(bits, "00000000000000000000100000", info);
    add_bitstring(bits, "00000100000000000000000000", info);
    add_bitstring(bits, "00000000000000010111110010", info);
    add_bitstring(bits, "00000000110000000000000000", info);
    add_bitstring(bits, "00100000000000000000000000", info);
    add_bitstring(bits, "00000000000000100000000000", info);
    add_bitstring(bits, "00001000000000000000000000", info);
    add_bitstring(bits, "00000000000001000000000000", info);
    add_bitstring(bits, "00000000000000000000010000", info);
    add_bitstring(bits, "00000000001000000000000000", info);
    add_bitstring(bits, "00000000100000000000000000", info);
    add_bitstring(bits, "00000000000000000010000000", info);
    add_bitstring(bits, "00000000100100000000000000", info);
    add_bitstring(bits, "00000010010000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(42);
    ts[0] = encrypt_input("11110111111111111011111101111111111110111101000000000000000000", info);
    ts[2] = encrypt_input("11110111111111111011110111111100000000000000011110110101111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[37];
    ctxt ss[76];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -9, gk, ss[0]); // __s0 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -11, gk, ss[1]); // __s1 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -16, gk, ss[2]); // __s2 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -20, gk, ss[3]); // __s3 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -23, gk, ss[4]); // __s4 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -5, gk, ss[5]); // __s5 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -8, gk, ss[6]); // __s6 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -15, gk, ss[7]); // __s7 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -22, gk, ss[8]); // __s8 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -1, gk, ss[9]); // __s9 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -7, gk, ss[10]); // __s10 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -12, gk, ss[11]); // __s11 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -21, gk, ss[12]); // __s12 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -24, gk, ss[13]); // __s13 = __v0 >> 24
    info.eval->rotate_rows(vs[0], -3, gk, ss[14]); // __s14 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -4, gk, ss[15]); // __s15 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -13, gk, ss[16]); // __s16 = __v0 >> 13
    info.eval->rotate_rows(vs[0], -14, gk, ss[17]); // __s17 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -17, gk, ss[18]); // __s18 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -19, gk, ss[19]); // __s19 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -18, gk, ss[20]); // __s20 = __v0 >> 18
    info.eval->rotate_rows(vs[0], -2, gk, ss[21]); // __s21 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -8, gk, ss[22]); // __s22 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -25, gk, ss[23]); // __s23 = __v1 >> 25
    info.eval->rotate_rows(vs[1], -6, gk, ss[24]); // __s24 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -23, gk, ss[25]); // __s25 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -17, gk, ss[26]); // __s26 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -3, gk, ss[27]); // __s27 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -22, gk, ss[28]); // __s28 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -20, gk, ss[29]); // __s29 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -14, gk, ss[30]); // __s30 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -7, gk, ss[31]); // __s31 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -4, gk, ss[32]); // __s32 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -1, gk, ss[33]); // __s33 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -13, gk, ss[34]); // __s34 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -12, gk, ss[35]); // __s35 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -5, gk, ss[36]); // __s36 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -21, gk, ss[37]); // __s37 = __v1 >> 21
    info.eval->rotate_rows(vs[1], -2, gk, ss[38]); // __s38 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -19, gk, ss[39]); // __s39 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -24, gk, ss[40]); // __s40 = __v1 >> 24
    info.eval->rotate_rows(vs[1], -16, gk, ss[41]); // __s41 = __v1 >> 16
    
    // __t4 = blend(__s19@10000000000000000000000000, __s14@00000001000000000000000000, __s6@00000000010000000000000000, __s1@00000000000010000000000000, __s10@00000000000001000000000000, __s7@00000000000000001000000000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6;
    info.eval->multiply_plain(ss[19], bits["10000000000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[14], bits["00000001000000000000000000"], t4_2);
    info.eval->multiply_plain(ss[6], bits["00000000010000000000000000"], t4_3);
    info.eval->multiply_plain(ss[1], bits["00000000000010000000000000"], t4_4);
    info.eval->multiply_plain(ss[10], bits["00000000000001000000000000"], t4_5);
    info.eval->multiply_plain(ss[7], bits["00000000000000001000000000"], t4_6);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6}, ts[4]);
    
    
    // __t5 = blend(__s37@10000000000000000000000000, __s32@00000001010000000000000000, __s31@00000000000010000000000000, __s41@00000000000001000000000000, __s30@00000000000000001000000000)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[37], bits["10000000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[32], bits["00000001010000000000000000"], t5_2);
    info.eval->multiply_plain(ss[31], bits["00000000000010000000000000"], t5_3);
    info.eval->multiply_plain(ss[41], bits["00000000000001000000000000"], t5_4);
    info.eval->multiply_plain(ss[30], bits["00000000000000001000000000"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -17, gk, ss[42]); // __s42 = __v2 >> 17
    info.eval->rotate_rows(vs[2], -9, gk, ss[43]); // __s43 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -11, gk, ss[44]); // __s44 = __v2 >> 11
    
    // __t6 = blend(__s9@00001000000000000000000000, __s15@00000000010000000000000000, __s21@00000000001000000000000000, __s2@00000000000000001000000000, __s16@00000000000000000100000000, __s20@00000000000000000000000001)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(ss[9], bits["00001000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[15], bits["00000000010000000000000000"], t6_2);
    info.eval->multiply_plain(ss[21], bits["00000000001000000000000000"], t6_3);
    info.eval->multiply_plain(ss[2], bits["00000000000000001000000000"], t6_4);
    info.eval->multiply_plain(ss[16], bits["00000000000000000100000000"], t6_5);
    info.eval->multiply_plain(ss[20], bits["00000000000000000000000001"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6}, ts[6]);
    
    
    // __t7 = blend(__s27@00001000000000000000000000, __s32@00000000010000000000000000, __s31@00000000001000000000000000, __s35@00000000000000001000000000, __s34@00000000000000000100000000, __s23@00000000000000000000000001)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6;
    info.eval->multiply_plain(ss[27], bits["00001000000000000000000000"], t7_1);
    info.eval->multiply_plain(ss[32], bits["00000000010000000000000000"], t7_2);
    info.eval->multiply_plain(ss[31], bits["00000000001000000000000000"], t7_3);
    info.eval->multiply_plain(ss[35], bits["00000000000000001000000000"], t7_4);
    info.eval->multiply_plain(ss[34], bits["00000000000000000100000000"], t7_5);
    info.eval->multiply_plain(ss[23], bits["00000000000000000000000001"], t7_6);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -16, gk, ss[45]); // __s45 = __v3 >> 16
    info.eval->rotate_rows(vs[3], -7, gk, ss[46]); // __s46 = __v3 >> 7
    info.eval->rotate_rows(vs[3], -1, gk, ss[47]); // __s47 = __v3 >> 1
    info.eval->rotate_rows(vs[3], -20, gk, ss[48]); // __s48 = __v3 >> 20
    
    // __t8 = blend(__s5@00000000010000000000000000, __s11@00000000000000100000000000, __s0@00000000000000010000000000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[5], bits["00000000010000000000000000"], t8_1);
    info.eval->multiply_plain(ss[11], bits["00000000000000100000000000"], t8_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000010000000000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s36@00000000010000000000000000, __s39@00000000000000100000000000, __s29@00000000000000010000000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[36], bits["00000000010000000000000000"], t9_1);
    info.eval->multiply_plain(ss[39], bits["00000000000000100000000000"], t9_2);
    info.eval->multiply_plain(ss[29], bits["00000000000000010000000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[49]); // __s49 = __v4 >> 1
    info.eval->rotate_rows(vs[4], -7, gk, ss[50]); // __s50 = __v4 >> 7
    info.eval->multiply(ss[15], ss[31], vs[5]); // __v5 = __s15 * __s31
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->add(vs[4], vs[5], vs[6]); // __v6 = __v4 + __v5
    info.eval->multiply(ss[10], ss[35], vs[7]); // __v7 = __s10 * __s35
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t10 = blend(__s4@00000100000000000000000000, __s0@00000000010000000000000000, __s12@00000000000000000000000010)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[4], bits["00000100000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[0], bits["00000000010000000000000000"], t10_2);
    info.eval->multiply_plain(ss[12], bits["00000000000000000000000010"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__s33@00000100000000000000000010, __s24@00000000010000000000000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(ss[33], bits["00000100000000000000000010"], t11_1);
    info.eval->multiply_plain(ss[24], bits["00000000010000000000000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[8]); // __v8 = __t10 * __t11
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -15, gk, ss[51]); // __s51 = __v8 >> 15
    info.eval->rotate_rows(vs[8], -19, gk, ss[52]); // __s52 = __v8 >> 19
    info.eval->multiply(ss[10], ss[22], vs[9]); // __v9 = __s10 * __s22
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->multiply(ss[6], ss[31], vs[10]); // __v10 = __s6 * __s31
    info.eval->relinearize_inplace(vs[10], rk);
    
    // __t12 = blend(__v8@00000000010000000000000000, __v3@00000000000000001000000000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[8], bits["00000000010000000000000000"], t12_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000001000000000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    info.eval->add(ts[12], vs[2], vs[11]); // __v11 = __t12 + __v2
    
    // __t13 = blend(__s13@01000000000000000000000000, __s0@00000000010000000000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[13], bits["01000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[0], bits["00000000010000000000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    
    // __t14 = blend(__s24@01000000000000000000000000, __s36@00000000010000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[24], bits["01000000000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[36], bits["00000000010000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[12]); // __v12 = __t13 * __t14
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -18, gk, ss[53]); // __s53 = __v12 >> 18
    info.eval->add(vs[12], vs[10], vs[13]); // __v13 = __v12 + __v10
    info.eval->add(vs[13], vs[9], vs[14]); // __v14 = __v13 + __v9
    info.eval->add(vs[11], vs[7], vs[15]); // __v15 = __v11 + __v7
    
    // __t15 = blend(__s5@00000010010000000000000000, __s17@00000000000000000001000000, __s16@00000000000000000000010000, __s18@00000000000000000000000100)
    ctxt t15_1, t15_2, t15_3, t15_4;
    info.eval->multiply_plain(ss[5], bits["00000010010000000000000000"], t15_1);
    info.eval->multiply_plain(ss[17], bits["00000000000000000001000000"], t15_2);
    info.eval->multiply_plain(ss[16], bits["00000000000000000000010000"], t15_3);
    info.eval->multiply_plain(ss[18], bits["00000000000000000000000100"], t15_4);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4}, ts[15]);
    
    
    // __t16 = blend(__s24@00000010010000000000000000, __s30@00000000000000000001000000, __s23@00000000000000000000010000, __s28@00000000000000000000000100)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(ss[24], bits["00000010010000000000000000"], t16_1);
    info.eval->multiply_plain(ss[30], bits["00000000000000000001000000"], t16_2);
    info.eval->multiply_plain(ss[23], bits["00000000000000000000010000"], t16_3);
    info.eval->multiply_plain(ss[28], bits["00000000000000000000000100"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4}, ts[16]);
    
    info.eval->multiply(ts[15], ts[16], vs[16]); // __v16 = __t15 * __t16
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->rotate_rows(vs[16], -9, gk, ss[54]); // __s54 = __v16 >> 9
    info.eval->rotate_rows(vs[16], -5, gk, ss[55]); // __s55 = __v16 >> 5
    info.eval->rotate_rows(vs[16], -24, gk, ss[56]); // __s56 = __v16 >> 24
    info.eval->rotate_rows(vs[16], -21, gk, ss[57]); // __s57 = __v16 >> 21
    info.eval->multiply(ss[14], ss[22], vs[17]); // __v17 = __s14 * __s22
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->add(vs[16], vs[3], vs[18]); // __v18 = __v16 + __v3
    
    // __t17 = blend(__s14@00000000110000000000000000, __s1@00000000000100000000000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[14], bits["00000000110000000000000000"], t17_1);
    info.eval->multiply_plain(ss[1], bits["00000000000100000000000000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    
    // __t18 = blend(__s22@00000000100100000000000000, __s35@00000000010000000000000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[22], bits["00000000100100000000000000"], t18_1);
    info.eval->multiply_plain(ss[35], bits["00000000010000000000000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(ts[17], ts[18], vs[19]); // __v19 = __t17 * __t18
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->rotate_rows(vs[19], -10, gk, ss[58]); // __s58 = __v19 >> 10
    info.eval->add(vs[18], vs[19], vs[20]); // __v20 = __v18 + __v19
    
    // __t19 = blend(__s4@00100000000000000000000000, __v20@00000000010000000000000000, __s7@00000000000000000000001000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(ss[4], bits["00100000000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[20], bits["00000000010000000000000000"], t19_2);
    info.eval->multiply_plain(ss[7], bits["00000000000000000000001000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    
    // __t20 = blend(__v1@00100000000000000000000000, __v14@00000000010000000000000000, __s29@00000000000000000000001000)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(vs[1], bits["00100000000000000000000000"], t20_1);
    info.eval->multiply_plain(vs[14], bits["00000000010000000000000000"], t20_2);
    info.eval->multiply_plain(ss[29], bits["00000000000000000000001000"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3}, ts[20]);
    
    info.eval->multiply(ts[19], ts[20], vs[21]); // __v21 = __t19 * __t20
    info.eval->relinearize_inplace(vs[21], rk);
    info.eval->rotate_rows(vs[21], -16, gk, ss[59]); // __s59 = __v21 >> 16
    info.eval->rotate_rows(vs[21], -24, gk, ss[60]); // __s60 = __v21 >> 24
    info.eval->add(vs[6], vs[17], vs[22]); // __v22 = __v6 + __v17
    
    // __t21 = blend(__s9@00010000000000000000000000, __s15@00000000100000000000000000, __v15@00000000010000000000000000, __s2@00000000000000000010000000, __s3@00000000000000000000100000)
    ctxt t21_1, t21_2, t21_3, t21_4, t21_5;
    info.eval->multiply_plain(ss[9], bits["00010000000000000000000000"], t21_1);
    info.eval->multiply_plain(ss[15], bits["00000000100000000000000000"], t21_2);
    info.eval->multiply_plain(vs[15], bits["00000000010000000000000000"], t21_3);
    info.eval->multiply_plain(ss[2], bits["00000000000000000010000000"], t21_4);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000100000"], t21_5);
    info.eval->add_many({t21_1, t21_2, t21_3, t21_4, t21_5}, ts[21]);
    
    
    // __t22 = blend(__s24@00010000000000000000000000, __s35@00000000100000000000000000, __v22@00000000010000000000000000, __s26@00000000000000000010000000, __s40@00000000000000000000100000)
    ctxt t22_1, t22_2, t22_3, t22_4, t22_5;
    info.eval->multiply_plain(ss[24], bits["00010000000000000000000000"], t22_1);
    info.eval->multiply_plain(ss[35], bits["00000000100000000000000000"], t22_2);
    info.eval->multiply_plain(vs[22], bits["00000000010000000000000000"], t22_3);
    info.eval->multiply_plain(ss[26], bits["00000000000000000010000000"], t22_4);
    info.eval->multiply_plain(ss[40], bits["00000000000000000000100000"], t22_5);
    info.eval->add_many({t22_1, t22_2, t22_3, t22_4, t22_5}, ts[22]);
    
    info.eval->multiply(ts[21], ts[22], vs[23]); // __v23 = __t21 * __t22
    info.eval->relinearize_inplace(vs[23], rk);
    info.eval->rotate_rows(vs[23], -18, gk, ss[61]); // __s61 = __v23 >> 18
    info.eval->rotate_rows(vs[23], -24, gk, ss[62]); // __s62 = __v23 >> 24
    info.eval->rotate_rows(vs[23], -21, gk, ss[63]); // __s63 = __v23 >> 21
    
    // __t23 = blend(__v19@00000000100000000000000000, __v21@00000000010000000000000000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(vs[19], bits["00000000100000000000000000"], t23_1);
    info.eval->multiply_plain(vs[21], bits["00000000010000000000000000"], t23_2);
    info.eval->add(t23_1, t23_2, ts[23]);
    
    info.eval->add(vs[23], ts[23], vs[24]); // __v24 = __v23 + __t23
    info.eval->rotate_rows(vs[24], -14, gk, ss[64]); // __s64 = __v24 >> 14
    info.eval->rotate_rows(vs[24], -12, gk, ss[65]); // __s65 = __v24 >> 12
    
    // __t24 = blend(__s63@00000000000000010000000000, __s46@00000000000000000100000000, __s47@00000000000000000010000000, __s56@00000000000000000001000000, __s51@00000000000000000000100000, __s58@00000000000000000000010000, __s64@00000000000000000000001000, __s42@00000000000000000000000010)
    ctxt t24_1, t24_2, t24_3, t24_4, t24_5, t24_6, t24_7, t24_8;
    info.eval->multiply_plain(ss[63], bits["00000000000000010000000000"], t24_1);
    info.eval->multiply_plain(ss[46], bits["00000000000000000100000000"], t24_2);
    info.eval->multiply_plain(ss[47], bits["00000000000000000010000000"], t24_3);
    info.eval->multiply_plain(ss[56], bits["00000000000000000001000000"], t24_4);
    info.eval->multiply_plain(ss[51], bits["00000000000000000000100000"], t24_5);
    info.eval->multiply_plain(ss[58], bits["00000000000000000000010000"], t24_6);
    info.eval->multiply_plain(ss[64], bits["00000000000000000000001000"], t24_7);
    info.eval->multiply_plain(ss[42], bits["00000000000000000000000010"], t24_8);
    info.eval->add_many({t24_1, t24_2, t24_3, t24_4, t24_5, t24_6, t24_7, t24_8}, ts[24]);
    
    
    // __t25 = blend(__s54@00000000000000010000000000, __s42@00000000000000000100000000, __s59@00000000000000000010000000, __s48@00000000000000000001000000, __s60@00000000000000000000100000, __s43@00000000000000000000010000, __s50@00000000000000000000001000, __s55@00000000000000000000000010)
    ctxt t25_1, t25_2, t25_3, t25_4, t25_5, t25_6, t25_7, t25_8;
    info.eval->multiply_plain(ss[54], bits["00000000000000010000000000"], t25_1);
    info.eval->multiply_plain(ss[42], bits["00000000000000000100000000"], t25_2);
    info.eval->multiply_plain(ss[59], bits["00000000000000000010000000"], t25_3);
    info.eval->multiply_plain(ss[48], bits["00000000000000000001000000"], t25_4);
    info.eval->multiply_plain(ss[60], bits["00000000000000000000100000"], t25_5);
    info.eval->multiply_plain(ss[43], bits["00000000000000000000010000"], t25_6);
    info.eval->multiply_plain(ss[50], bits["00000000000000000000001000"], t25_7);
    info.eval->multiply_plain(ss[55], bits["00000000000000000000000010"], t25_8);
    info.eval->add_many({t25_1, t25_2, t25_3, t25_4, t25_5, t25_6, t25_7, t25_8}, ts[25]);
    
    info.eval->add(ts[24], ts[25], vs[25]); // __v25 = __t24 + __t25
    
    // __t26 = blend(__v25@00000000000000010111110010, __v11@00000000000000001000000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(vs[25], bits["00000000000000010111110010"], t26_1);
    info.eval->multiply_plain(vs[11], bits["00000000000000001000000000"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__s49@00000000000000010000000000, __s62@00000000000000001000000000, __s52@00000000000000000100000000, __s57@00000000000000000010000000, __s53@00000000000000000001000000, __s45@00000000000000000000100000, __s61@00000000000000000000010000, __s44@00000000000000000000000010)
    ctxt t27_1, t27_2, t27_3, t27_4, t27_5, t27_6, t27_7, t27_8;
    info.eval->multiply_plain(ss[49], bits["00000000000000010000000000"], t27_1);
    info.eval->multiply_plain(ss[62], bits["00000000000000001000000000"], t27_2);
    info.eval->multiply_plain(ss[52], bits["00000000000000000100000000"], t27_3);
    info.eval->multiply_plain(ss[57], bits["00000000000000000010000000"], t27_4);
    info.eval->multiply_plain(ss[53], bits["00000000000000000001000000"], t27_5);
    info.eval->multiply_plain(ss[45], bits["00000000000000000000100000"], t27_6);
    info.eval->multiply_plain(ss[61], bits["00000000000000000000010000"], t27_7);
    info.eval->multiply_plain(ss[44], bits["00000000000000000000000010"], t27_8);
    info.eval->add_many({t27_1, t27_2, t27_3, t27_4, t27_5, t27_6, t27_7, t27_8}, ts[27]);
    
    info.eval->add(ts[26], ts[27], vs[26]); // __v26 = __t26 + __t27
    info.eval->rotate_rows(vs[26], -9, gk, ss[66]); // __s66 = __v26 >> 9
    info.eval->rotate_rows(vs[26], -3, gk, ss[67]); // __s67 = __v26 >> 3
    info.eval->rotate_rows(vs[26], -5, gk, ss[68]); // __s68 = __v26 >> 5
    info.eval->rotate_rows(vs[26], -2, gk, ss[69]); // __s69 = __v26 >> 2
    info.eval->rotate_rows(vs[26], -1, gk, ss[70]); // __s70 = __v26 >> 1
    
    // __t28 = blend(__v25@00000000000000000000001000, __s8@00000000000000000000000100, __s66@00000000000000000000000010, __s12@00000000000000000000000001)
    ctxt t28_1, t28_2, t28_3, t28_4;
    info.eval->multiply_plain(vs[25], bits["00000000000000000000001000"], t28_1);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000000100"], t28_2);
    info.eval->multiply_plain(ss[66], bits["00000000000000000000000010"], t28_3);
    info.eval->multiply_plain(ss[12], bits["00000000000000000000000001"], t28_4);
    info.eval->add_many({t28_1, t28_2, t28_3, t28_4}, ts[28]);
    
    
    // __t29 = blend(__s70@00000000000000000000001000, __s25@00000000000000000000000100, __v26@00000000000000000000000010, __s27@00000000000000000000000001)
    ctxt t29_1, t29_2, t29_3, t29_4;
    info.eval->multiply_plain(ss[70], bits["00000000000000000000001000"], t29_1);
    info.eval->multiply_plain(ss[25], bits["00000000000000000000000100"], t29_2);
    info.eval->multiply_plain(vs[26], bits["00000000000000000000000010"], t29_3);
    info.eval->multiply_plain(ss[27], bits["00000000000000000000000001"], t29_4);
    info.eval->add_many({t29_1, t29_2, t29_3, t29_4}, ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[27]); // __v27 = __t28 * __t29
    info.eval->relinearize_inplace(vs[27], rk);
    info.eval->rotate_rows(vs[27], -24, gk, ss[71]); // __s71 = __v27 >> 24
    
    // __t30 = blend(__s12@00000000000000000000000100, __s3@00000000000000000000000001)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(ss[12], bits["00000000000000000000000100"], t30_1);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000000001"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    
    // __t31 = blend(__s38@00000000000000000000000100, __s23@00000000000000000000000001)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(ss[38], bits["00000000000000000000000100"], t31_1);
    info.eval->multiply_plain(ss[23], bits["00000000000000000000000001"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[28]); // __v28 = __t30 * __t31
    info.eval->relinearize_inplace(vs[28], rk);
    
    // __t32 = blend(__s4@00000000000000000000000100, __s19@00000000000000000000000001)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(ss[4], bits["00000000000000000000000100"], t32_1);
    info.eval->multiply_plain(ss[19], bits["00000000000000000000000001"], t32_2);
    info.eval->add(t32_1, t32_2, ts[32]);
    
    
    // __t33 = blend(__s33@00000000000000000000000100, __s32@00000000000000000000000001)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(ss[33], bits["00000000000000000000000100"], t33_1);
    info.eval->multiply_plain(ss[32], bits["00000000000000000000000001"], t33_2);
    info.eval->add(t33_1, t33_2, ts[33]);
    
    info.eval->multiply(ts[32], ts[33], vs[29]); // __v29 = __t32 * __t33
    info.eval->relinearize_inplace(vs[29], rk);
    
    // __t34 = blend(__v29@00000000000000000000000100, __v27@00000000000000000000000001)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[29], bits["00000000000000000000000100"], t34_1);
    info.eval->multiply_plain(vs[27], bits["00000000000000000000000001"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    
    // __t35 = blend(__v27@00000000000000000000000100, __v28@00000000000000000000000001)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[27], bits["00000000000000000000000100"], t35_1);
    info.eval->multiply_plain(vs[28], bits["00000000000000000000000001"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->add(ts[34], ts[35], vs[30]); // __v30 = __t34 + __t35
    
    // __t36 = blend(__v28@00000000000000000000000100, __v29@00000000000000000000000001)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(vs[28], bits["00000000000000000000000100"], t36_1);
    info.eval->multiply_plain(vs[29], bits["00000000000000000000000001"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    info.eval->add(vs[30], ts[36], vs[31]); // __v31 = __v30 + __t36
    
    // __t37 = blend(__s68@00000000000000000000000100, __s66@00000000000000000000000001)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(ss[68], bits["00000000000000000000000100"], t37_1);
    info.eval->multiply_plain(ss[66], bits["00000000000000000000000001"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    info.eval->multiply(vs[31], ts[37], vs[32]); // __v32 = __v31 * __t37
    info.eval->relinearize_inplace(vs[32], rk);
    info.eval->rotate_rows(vs[32], -23, gk, ss[72]); // __s72 = __v32 >> 23
    info.eval->rotate_rows(vs[32], -21, gk, ss[73]); // __s73 = __v32 >> 21
    
    // __t38 = blend(__s72@00000000000000000000100000, __s71@00000000000000000000001000)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(ss[72], bits["00000000000000000000100000"], t38_1);
    info.eval->multiply_plain(ss[71], bits["00000000000000000000001000"], t38_2);
    info.eval->add(t38_1, t38_2, ts[38]);
    
    
    // __t39 = blend(__s73@00000000000000000000100000, __v27@00000000000000000000001000)
    ctxt t39_1, t39_2;
    info.eval->multiply_plain(ss[73], bits["00000000000000000000100000"], t39_1);
    info.eval->multiply_plain(vs[27], bits["00000000000000000000001000"], t39_2);
    info.eval->add(t39_1, t39_2, ts[39]);
    
    info.eval->add(ts[38], ts[39], vs[33]); // __v33 = __t38 + __t39
    
    // __t40 = blend(__s67@00000000000000000000100000, __s69@00000000000000000000011000)
    ctxt t40_1, t40_2;
    info.eval->multiply_plain(ss[67], bits["00000000000000000000100000"], t40_1);
    info.eval->multiply_plain(ss[69], bits["00000000000000000000011000"], t40_2);
    info.eval->add(t40_1, t40_2, ts[40]);
    
    
    // __t41 = blend(__v33@00000000000000000000101000, __s65@00000000000000000000010000)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(vs[33], bits["00000000000000000000101000"], t41_1);
    info.eval->multiply_plain(ss[65], bits["00000000000000000000010000"], t41_2);
    info.eval->add(t41_1, t41_2, ts[41]);
    
    info.eval->multiply(ts[40], ts[41], vs[34]); // __v34 = __t40 * __t41
    info.eval->relinearize_inplace(vs[34], rk);
    info.eval->rotate_rows(vs[34], -2, gk, ss[74]); // __s74 = __v34 >> 2
    info.eval->rotate_rows(vs[34], -1, gk, ss[75]); // __s75 = __v34 >> 1
    info.eval->sub(ss[75], ss[74], vs[35]); // __v35 = __s75 - __s74
    info.eval->add(vs[35], vs[34], vs[36]); // __v36 = __v35 + __v34
    return vs[36];
}
    