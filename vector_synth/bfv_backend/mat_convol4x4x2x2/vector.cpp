
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000010000000000000000000", info);
    add_bitstring(bits, "0000000000000000110000000000", info);
    add_bitstring(bits, "0000000001000001000000000000", info);
    add_bitstring(bits, "0000000000000000000000000001", info);
    add_bitstring(bits, "0000000000000001000000000000", info);
    add_bitstring(bits, "0000000000000000000000000100", info);
    add_bitstring(bits, "0000001000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000000100000", info);
    add_bitstring(bits, "0001000000000000000000000000", info);
    add_bitstring(bits, "0000000000000000010000000000", info);
    add_bitstring(bits, "0000000000010000000000000000", info);
    add_bitstring(bits, "0000000000000000000001000000", info);
    add_bitstring(bits, "0010000000010000000000001000", info);
    add_bitstring(bits, "1000000000000000000000000000", info);
    add_bitstring(bits, "0000000000000000100000000000", info);
    add_bitstring(bits, "0000000000000000000000001000", info);
    add_bitstring(bits, "0000000000000000001000000000", info);
    add_bitstring(bits, "0000000100000000000000000000", info);
    add_bitstring(bits, "0100000000000000000000000000", info);
    add_bitstring(bits, "1000001001101000000000000000", info);
    add_bitstring(bits, "0000010000000000000000000000", info);
    add_bitstring(bits, "0011000000000000000000000000", info);
    add_bitstring(bits, "0000000000100000000000000000", info);
    add_bitstring(bits, "0000000000000000000000000010", info);
    add_bitstring(bits, "0000000000000100000000000000", info);
    add_bitstring(bits, "0000000000000000000100000000", info);
    add_bitstring(bits, "0000010000000000000000000100", info);
    add_bitstring(bits, "0000000001000000000000000000", info);
    add_bitstring(bits, "0000000000001000000000000000", info);
    add_bitstring(bits, "0000000000000000000010000000", info);
    add_bitstring(bits, "0000000000000000000000010000", info);
    add_bitstring(bits, "0000000000000000000000000110", info);
    add_bitstring(bits, "0000100000000000000000000000", info);
    add_bitstring(bits, "0000000000000010000000000000", info);
    add_bitstring(bits, "0000000000000000001000100000", info);
    add_bitstring(bits, "0000000010000100000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(20);
    ts[0] = encrypt_input("11111111111111011011111111101111111111101111111010011111000111110111101111100001111111011000", info);
    ts[2] = encrypt_input("00000110111111100110101111000000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[67];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -12, gk, ss[0]); // __s0 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -5, gk, ss[1]); // __s1 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -24, gk, ss[2]); // __s2 = __v0 >> 24
    info.eval->rotate_rows(vs[0], -18, gk, ss[3]); // __s3 = __v0 >> 18
    info.eval->rotate_rows(vs[0], -6, gk, ss[4]); // __s4 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -7, gk, ss[5]); // __s5 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -1, gk, ss[6]); // __s6 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -15, gk, ss[7]); // __s7 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -16, gk, ss[8]); // __s8 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -19, gk, ss[9]); // __s9 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -21, gk, ss[10]); // __s10 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -23, gk, ss[11]); // __s11 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -11, gk, ss[12]); // __s12 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -3, gk, ss[13]); // __s13 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -14, gk, ss[14]); // __s14 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -17, gk, ss[15]); // __s15 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -20, gk, ss[16]); // __s16 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -25, gk, ss[17]); // __s17 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -22, gk, ss[18]); // __s18 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -8, gk, ss[19]); // __s19 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -4, gk, ss[20]); // __s20 = __v0 >> 4
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -3, gk, ss[21]); // __s21 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -8, gk, ss[22]); // __s22 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -13, gk, ss[23]); // __s23 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -14, gk, ss[24]); // __s24 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -19, gk, ss[25]); // __s25 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -20, gk, ss[26]); // __s26 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -22, gk, ss[27]); // __s27 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -24, gk, ss[28]); // __s28 = __v1 >> 24
    info.eval->rotate_rows(vs[1], -1, gk, ss[29]); // __s29 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -4, gk, ss[30]); // __s30 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -5, gk, ss[31]); // __s31 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -9, gk, ss[32]); // __s32 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -17, gk, ss[33]); // __s33 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -27, gk, ss[34]); // __s34 = __v1 >> 27
    info.eval->rotate_rows(vs[1], -7, gk, ss[35]); // __s35 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -12, gk, ss[36]); // __s36 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -16, gk, ss[37]); // __s37 = __v1 >> 16
    info.eval->rotate_rows(vs[1], -18, gk, ss[38]); // __s38 = __v1 >> 18
    info.eval->rotate_rows(vs[1], -21, gk, ss[39]); // __s39 = __v1 >> 21
    info.eval->rotate_rows(vs[1], -2, gk, ss[40]); // __s40 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -10, gk, ss[41]); // __s41 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -15, gk, ss[42]); // __s42 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -23, gk, ss[43]); // __s43 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -26, gk, ss[44]); // __s44 = __v1 >> 26
    
    // __t4 = blend(__s27@0000100000000000000000000000, __s28@0000010000000000000000000000, __v1@0000001000000000000000000000, __s44@0000000010000000000000000000, __s37@0000000000000000000000000100, __s38@0000000000000000000000000001)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6;
    info.eval->multiply_plain(ss[27], bits["0000100000000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[28], bits["0000010000000000000000000000"], t4_2);
    info.eval->multiply_plain(vs[1], bits["0000001000000000000000000000"], t4_3);
    info.eval->multiply_plain(ss[44], bits["0000000010000000000000000000"], t4_4);
    info.eval->multiply_plain(ss[37], bits["0000000000000000000000000100"], t4_5);
    info.eval->multiply_plain(ss[38], bits["0000000000000000000000000001"], t4_6);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6}, ts[4]);
    
    
    // __t5 = blend(__s10@0000100000000000000000000000, __s17@0000010000000000000000000000, __v0@0000001000000000000000000000, __s5@0000000010000000000000000000, __s2@0000000000000000000000000100, __s11@0000000000000000000000000001)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6;
    info.eval->multiply_plain(ss[10], bits["0000100000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[17], bits["0000010000000000000000000000"], t5_2);
    info.eval->multiply_plain(vs[0], bits["0000001000000000000000000000"], t5_3);
    info.eval->multiply_plain(ss[5], bits["0000000010000000000000000000"], t5_4);
    info.eval->multiply_plain(ss[2], bits["0000000000000000000000000100"], t5_5);
    info.eval->multiply_plain(ss[11], bits["0000000000000000000000000001"], t5_6);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -4, gk, ss[45]); // __s45 = __v2 >> 4
    
    // __t6 = blend(__s28@0100000000000000000000000000, __s39@0011000000000000000000000000, __v1@0000010000000000000000000000, __s21@0000000010000000000000000000, __s31@0000000000010000000000000000, __s40@0000000000001000000000000000, __s23@0000000000000000001000000000, __s24@0000000000000000000100000000, __s41@0000000000000000000010000000, __s36@0000000000000000000000100000, __s33@0000000000000000000000010000, __s25@0000000000000000000000001000, __s27@0000000000000000000000000001)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7, t6_8, t6_9, t6_10, t6_11, t6_12, t6_13;
    info.eval->multiply_plain(ss[28], bits["0100000000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[39], bits["0011000000000000000000000000"], t6_2);
    info.eval->multiply_plain(vs[1], bits["0000010000000000000000000000"], t6_3);
    info.eval->multiply_plain(ss[21], bits["0000000010000000000000000000"], t6_4);
    info.eval->multiply_plain(ss[31], bits["0000000000010000000000000000"], t6_5);
    info.eval->multiply_plain(ss[40], bits["0000000000001000000000000000"], t6_6);
    info.eval->multiply_plain(ss[23], bits["0000000000000000001000000000"], t6_7);
    info.eval->multiply_plain(ss[24], bits["0000000000000000000100000000"], t6_8);
    info.eval->multiply_plain(ss[41], bits["0000000000000000000010000000"], t6_9);
    info.eval->multiply_plain(ss[36], bits["0000000000000000000000100000"], t6_10);
    info.eval->multiply_plain(ss[33], bits["0000000000000000000000010000"], t6_11);
    info.eval->multiply_plain(ss[25], bits["0000000000000000000000001000"], t6_12);
    info.eval->multiply_plain(ss[27], bits["0000000000000000000000000001"], t6_13);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7, t6_8, t6_9, t6_10, t6_11, t6_12, t6_13}, ts[6]);
    
    
    // __t7 = blend(__s14@0100000000000000000000000000, __v0@0010000000010000000000001000, __s6@0001000000000000000000000000, __s18@0000010000000000000000000000, __s13@0000000010000000000000000000, __s0@0000000000001000000000000000, __s7@0000000000000000001000100000, __s3@0000000000000000000100000000, __s8@0000000000000000000010000000, __s9@0000000000000000000000010000, __s20@0000000000000000000000000001)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8, t7_9, t7_10, t7_11;
    info.eval->multiply_plain(ss[14], bits["0100000000000000000000000000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["0010000000010000000000001000"], t7_2);
    info.eval->multiply_plain(ss[6], bits["0001000000000000000000000000"], t7_3);
    info.eval->multiply_plain(ss[18], bits["0000010000000000000000000000"], t7_4);
    info.eval->multiply_plain(ss[13], bits["0000000010000000000000000000"], t7_5);
    info.eval->multiply_plain(ss[0], bits["0000000000001000000000000000"], t7_6);
    info.eval->multiply_plain(ss[7], bits["0000000000000000001000100000"], t7_7);
    info.eval->multiply_plain(ss[3], bits["0000000000000000000100000000"], t7_8);
    info.eval->multiply_plain(ss[8], bits["0000000000000000000010000000"], t7_9);
    info.eval->multiply_plain(ss[9], bits["0000000000000000000000010000"], t7_10);
    info.eval->multiply_plain(ss[20], bits["0000000000000000000000000001"], t7_11);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8, t7_9, t7_10, t7_11}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -5, gk, ss[46]); // __s46 = __v3 >> 5
    info.eval->rotate_rows(vs[3], -10, gk, ss[47]); // __s47 = __v3 >> 10
    info.eval->rotate_rows(vs[3], -25, gk, ss[48]); // __s48 = __v3 >> 25
    info.eval->rotate_rows(vs[3], -22, gk, ss[49]); // __s49 = __v3 >> 22
    info.eval->rotate_rows(vs[3], -19, gk, ss[50]); // __s50 = __v3 >> 19
    info.eval->rotate_rows(vs[3], -9, gk, ss[51]); // __s51 = __v3 >> 9
    info.eval->rotate_rows(vs[3], -18, gk, ss[52]); // __s52 = __v3 >> 18
    info.eval->rotate_rows(vs[3], -15, gk, ss[53]); // __s53 = __v3 >> 15
    info.eval->rotate_rows(vs[3], -12, gk, ss[54]); // __s54 = __v3 >> 12
    info.eval->rotate_rows(vs[3], -14, gk, ss[55]); // __s55 = __v3 >> 14
    info.eval->add(vs[2], vs[3], vs[4]); // __v4 = __v2 + __v3
    info.eval->rotate_rows(vs[4], -9, gk, ss[56]); // __s56 = __v4 >> 9
    
    // __t8 = blend(__s27@1000000000000000000000000000, __s43@0000010000000000000000000000, __s34@0000000010000000000000000000, __v1@0000000001000000000000000000, __s22@0000000000000100000000000000, __s32@0000000000000001000000000000, __s26@0000000000000000000000000110)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7;
    info.eval->multiply_plain(ss[27], bits["1000000000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[43], bits["0000010000000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[34], bits["0000000010000000000000000000"], t8_3);
    info.eval->multiply_plain(vs[1], bits["0000000001000000000000000000"], t8_4);
    info.eval->multiply_plain(ss[22], bits["0000000000000100000000000000"], t8_5);
    info.eval->multiply_plain(ss[32], bits["0000000000000001000000000000"], t8_6);
    info.eval->multiply_plain(ss[26], bits["0000000000000000000000000110"], t8_7);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7}, ts[8]);
    
    
    // __t9 = blend(__s16@1000000000000000000000000000, __s7@0000010000000000000000000000, __s1@0000000010000100000000000000, __v0@0000000001000001000000000000, __s10@0000000000000000000000000100, __s19@0000000000000000000000000010)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6;
    info.eval->multiply_plain(ss[16], bits["1000000000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[7], bits["0000010000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[1], bits["0000000010000100000000000000"], t9_3);
    info.eval->multiply_plain(vs[0], bits["0000000001000001000000000000"], t9_4);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000000000100"], t9_5);
    info.eval->multiply_plain(ss[19], bits["0000000000000000000000000010"], t9_6);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[5]); // __v5 = __t8 * __t9
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -27, gk, ss[57]); // __s57 = __v5 >> 27
    info.eval->rotate_rows(vs[5], -21, gk, ss[58]); // __s58 = __v5 >> 21
    info.eval->rotate_rows(vs[5], -14, gk, ss[59]); // __s59 = __v5 >> 14
    
    // __t10 = blend(__v4@0000010000000000000000000000, __v5@0000000010000000000000000000, __v2@0000000000000000000000000100)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[4], bits["0000010000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[5], bits["0000000010000000000000000000"], t10_2);
    info.eval->multiply_plain(vs[2], bits["0000000000000000000000000100"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v5@0000010000000000000000000100, __v3@0000000010000000000000000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[5], bits["0000010000000000000000000100"], t11_1);
    info.eval->multiply_plain(vs[3], bits["0000000010000000000000000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[6]); // __v6 = __t10 + __t11
    
    // __t12 = blend(__s34@0000010000000000000000000000, __s29@0000000100000000000000000000, __s30@0000000000100000000000000000, __s31@0000000000000010000000000000, __s35@0000000000000000110000000000, __s36@0000000000000000000001000000, __s42@0000000000000000000000000100)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5, t12_6, t12_7;
    info.eval->multiply_plain(ss[34], bits["0000010000000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[29], bits["0000000100000000000000000000"], t12_2);
    info.eval->multiply_plain(ss[30], bits["0000000000100000000000000000"], t12_3);
    info.eval->multiply_plain(ss[31], bits["0000000000000010000000000000"], t12_4);
    info.eval->multiply_plain(ss[35], bits["0000000000000000110000000000"], t12_5);
    info.eval->multiply_plain(ss[36], bits["0000000000000000000001000000"], t12_6);
    info.eval->multiply_plain(ss[42], bits["0000000000000000000000000100"], t12_7);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5, t12_6, t12_7}, ts[12]);
    
    
    // __t13 = blend(__s1@0000010000000000000000000000, __s4@0000000100000000000000000000, __s7@0000000000100000000000000000, __s13@0000000000000010000000000000, __s12@0000000000000000100000000000, __v0@0000000000000000010000000000, __s14@0000000000000000000001000000, __s15@0000000000000000000000000100)
    ctxt t13_1, t13_2, t13_3, t13_4, t13_5, t13_6, t13_7, t13_8;
    info.eval->multiply_plain(ss[1], bits["0000010000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[4], bits["0000000100000000000000000000"], t13_2);
    info.eval->multiply_plain(ss[7], bits["0000000000100000000000000000"], t13_3);
    info.eval->multiply_plain(ss[13], bits["0000000000000010000000000000"], t13_4);
    info.eval->multiply_plain(ss[12], bits["0000000000000000100000000000"], t13_5);
    info.eval->multiply_plain(vs[0], bits["0000000000000000010000000000"], t13_6);
    info.eval->multiply_plain(ss[14], bits["0000000000000000000001000000"], t13_7);
    info.eval->multiply_plain(ss[15], bits["0000000000000000000000000100"], t13_8);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4, t13_5, t13_6, t13_7, t13_8}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[7]); // __v7 = __t12 * __t13
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -2, gk, ss[60]); // __s60 = __v7 >> 2
    info.eval->rotate_rows(vs[7], -20, gk, ss[61]); // __s61 = __v7 >> 20
    info.eval->rotate_rows(vs[7], -22, gk, ss[62]); // __s62 = __v7 >> 22
    info.eval->rotate_rows(vs[7], -23, gk, ss[63]); // __s63 = __v7 >> 23
    info.eval->rotate_rows(vs[7], -7, gk, ss[64]); // __s64 = __v7 >> 7
    
    // __t14 = blend(__v7@0000010000000000000000000100, __v2@0000000010000000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[7], bits["0000010000000000000000000100"], t14_1);
    info.eval->multiply_plain(vs[2], bits["0000000010000000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->add(vs[6], ts[14], vs[8]); // __v8 = __v6 + __t14
    info.eval->rotate_rows(vs[8], -27, gk, ss[65]); // __s65 = __v8 >> 27
    info.eval->rotate_rows(vs[8], -14, gk, ss[66]); // __s66 = __v8 >> 14
    
    // __t15 = blend(__s64@1000000000000000000000000000, __s61@0000001000000000000000000000, __s56@0000000010000000000000000000, __v5@0000000001000000000000000000, __s62@0000000000100000000000000000, __s47@0000000000001000000000000000)
    ctxt t15_1, t15_2, t15_3, t15_4, t15_5, t15_6;
    info.eval->multiply_plain(ss[64], bits["1000000000000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[61], bits["0000001000000000000000000000"], t15_2);
    info.eval->multiply_plain(ss[56], bits["0000000010000000000000000000"], t15_3);
    info.eval->multiply_plain(vs[5], bits["0000000001000000000000000000"], t15_4);
    info.eval->multiply_plain(ss[62], bits["0000000000100000000000000000"], t15_5);
    info.eval->multiply_plain(ss[47], bits["0000000000001000000000000000"], t15_6);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4, t15_5, t15_6}, ts[15]);
    
    
    // __t16 = blend(__s51@1000000000000000000000000000, __s46@0000001000000000000000000000, __s45@0000000010000000000000000000, __s50@0000000001000000000000000000, __s55@0000000000100000000000000000, __s57@0000000000001000000000000000)
    ctxt t16_1, t16_2, t16_3, t16_4, t16_5, t16_6;
    info.eval->multiply_plain(ss[51], bits["1000000000000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[46], bits["0000001000000000000000000000"], t16_2);
    info.eval->multiply_plain(ss[45], bits["0000000010000000000000000000"], t16_3);
    info.eval->multiply_plain(ss[50], bits["0000000001000000000000000000"], t16_4);
    info.eval->multiply_plain(ss[55], bits["0000000000100000000000000000"], t16_5);
    info.eval->multiply_plain(ss[57], bits["0000000000001000000000000000"], t16_6);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, t16_5, t16_6}, ts[16]);
    
    info.eval->add(ts[15], ts[16], vs[9]); // __v9 = __t15 + __t16
    
    // __t17 = blend(__s48@1000000000000000000000000000, __s49@0000001000000000000000000000, __s58@0000000010000000000000000000, __s53@0000000001000000000000000000, __s52@0000000000100000000000000000, __s63@0000000000001000000000000000)
    ctxt t17_1, t17_2, t17_3, t17_4, t17_5, t17_6;
    info.eval->multiply_plain(ss[48], bits["1000000000000000000000000000"], t17_1);
    info.eval->multiply_plain(ss[49], bits["0000001000000000000000000000"], t17_2);
    info.eval->multiply_plain(ss[58], bits["0000000010000000000000000000"], t17_3);
    info.eval->multiply_plain(ss[53], bits["0000000001000000000000000000"], t17_4);
    info.eval->multiply_plain(ss[52], bits["0000000000100000000000000000"], t17_5);
    info.eval->multiply_plain(ss[63], bits["0000000000001000000000000000"], t17_6);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4, t17_5, t17_6}, ts[17]);
    
    info.eval->add(vs[9], ts[17], vs[10]); // __v10 = __v9 + __t17
    
    // __t18 = blend(__v10@1000001001101000000000000000, __s65@0000000100000000000000000000, __s66@0000000000010000000000000000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[10], bits["1000001001101000000000000000"], t18_1);
    info.eval->multiply_plain(ss[65], bits["0000000100000000000000000000"], t18_2);
    info.eval->multiply_plain(ss[66], bits["0000000000010000000000000000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    
    // __t19 = blend(__v5@1000000000000000000000000000, __v2@0000001000000000000000000000, __s54@0000000100000000000000000000, __s60@0000000001000000000000000000, __v7@0000000000100000000000000000, __v3@0000000000010000000000000000, __s59@0000000000001000000000000000)
    ctxt t19_1, t19_2, t19_3, t19_4, t19_5, t19_6, t19_7;
    info.eval->multiply_plain(vs[5], bits["1000000000000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[2], bits["0000001000000000000000000000"], t19_2);
    info.eval->multiply_plain(ss[54], bits["0000000100000000000000000000"], t19_3);
    info.eval->multiply_plain(ss[60], bits["0000000001000000000000000000"], t19_4);
    info.eval->multiply_plain(vs[7], bits["0000000000100000000000000000"], t19_5);
    info.eval->multiply_plain(vs[3], bits["0000000000010000000000000000"], t19_6);
    info.eval->multiply_plain(ss[59], bits["0000000000001000000000000000"], t19_7);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4, t19_5, t19_6, t19_7}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[11]); // __v11 = __t18 + __t19
    return vs[11];
}
    