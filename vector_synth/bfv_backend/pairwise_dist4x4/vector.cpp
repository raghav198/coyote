
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000110000000000000000000", info);
    add_bitstring(bits, "0000000000000000000010000000", info);
    add_bitstring(bits, "0000000001000000000000000000", info);
    add_bitstring(bits, "0000001000000000000000000000", info);
    add_bitstring(bits, "1101000000000000000000000000", info);
    add_bitstring(bits, "0000000000001000000001000000", info);
    add_bitstring(bits, "0100000000000000000000000000", info);
    add_bitstring(bits, "0000000000000100000000000010", info);
    add_bitstring(bits, "0001000000000000000000000000", info);
    add_bitstring(bits, "0000000000000100000000000000", info);
    add_bitstring(bits, "0000000000000110000000000000", info);
    add_bitstring(bits, "0000000000000000100000000000", info);
    add_bitstring(bits, "1000000000000000000000000000", info);
    add_bitstring(bits, "0000100000000000000000000000", info);
    add_bitstring(bits, "1100000000000000000000000000", info);
    add_bitstring(bits, "0000000000000000001000000000", info);
    add_bitstring(bits, "0000000000010000000000000000", info);
    add_bitstring(bits, "0000000000000000000000001000", info);
    add_bitstring(bits, "0000000000000000000001000000", info);
    add_bitstring(bits, "0000000100000000000001000000", info);
    add_bitstring(bits, "0000001001000000000000000000", info);
    add_bitstring(bits, "0000000000110000000000000000", info);
    add_bitstring(bits, "0001010000000000000000000000", info);
    add_bitstring(bits, "0000000000100000000000000000", info);
    add_bitstring(bits, "0000000000000000010000000000", info);
    add_bitstring(bits, "0000000000000000000100000000", info);
    add_bitstring(bits, "0010000000000000000000000000", info);
    add_bitstring(bits, "0000000001100000000000000000", info);
    add_bitstring(bits, "0000000100000000000000000000", info);
    add_bitstring(bits, "0000010000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000000000001", info);
    add_bitstring(bits, "0000000000000000000000000010", info);
    add_bitstring(bits, "0000000000001000000000000000", info);
    add_bitstring(bits, "0000000000000001000000000000", info);
    add_bitstring(bits, "0000000000000000000000010000", info);
    add_bitstring(bits, "0000000000000100000000001000", info);
    add_bitstring(bits, "1000000001000000000000000000", info);
    add_bitstring(bits, "0000000001000000010000000000", info);
    add_bitstring(bits, "0000000010000000000000000000", info);
    add_bitstring(bits, "0000000000000000000000000100", info);
    add_bitstring(bits, "0000000000000010000000000000", info);
    add_bitstring(bits, "0000000000000000000000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(51);
    ts[0] = encrypt_input("000000011100000001111111100000000000", info);
    ts[1] = encrypt_input("000000011100000001111111100000000000", info);
    ts[2] = encrypt_input("000000000111111110011100000000000000", info);
    ts[3] = encrypt_input("000000000111111110011100000000000000", info);
    ts[4] = encrypt_input("001100000000001110011111100000000000", info);
    ts[5] = encrypt_input("001100000000001110011111100000000000", info);
    ts[6] = encrypt_input("000000111110011111100000000000000000", info);
    ts[7] = encrypt_input("000000111110011111100000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[42];
    ctxt ss[54];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -17, gk, ss[0]); // __s0 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -15, gk, ss[1]); // __s1 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -5, gk, ss[2]); // __s2 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -7, gk, ss[3]); // __s3 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -10, gk, ss[4]); // __s4 = __v0 >> 10
    info.eval->rotate_rows(vs[0], -19, gk, ss[5]); // __s5 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -20, gk, ss[6]); // __s6 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -22, gk, ss[7]); // __s7 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -25, gk, ss[8]); // __s8 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -9, gk, ss[9]); // __s9 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -6, gk, ss[10]); // __s10 = __v0 >> 6
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -10, gk, ss[11]); // __s11 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -19, gk, ss[12]); // __s12 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -20, gk, ss[13]); // __s13 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -22, gk, ss[14]); // __s14 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -3, gk, ss[15]); // __s15 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -5, gk, ss[16]); // __s16 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -16, gk, ss[17]); // __s17 = __v1 >> 16
    info.eval->rotate_rows(vs[1], -9, gk, ss[18]); // __s18 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -6, gk, ss[19]); // __s19 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -1, gk, ss[20]); // __s20 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -11, gk, ss[21]); // __s21 = __v1 >> 11
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -5, gk, ss[22]); // __s22 = __v2 >> 5
    info.eval->rotate_rows(vs[2], -11, gk, ss[23]); // __s23 = __v2 >> 11
    info.eval->rotate_rows(vs[2], -12, gk, ss[24]); // __s24 = __v2 >> 12
    info.eval->rotate_rows(vs[2], -21, gk, ss[25]); // __s25 = __v2 >> 21
    info.eval->rotate_rows(vs[2], -24, gk, ss[26]); // __s26 = __v2 >> 24
    info.eval->rotate_rows(vs[2], -27, gk, ss[27]); // __s27 = __v2 >> 27
    info.eval->rotate_rows(vs[2], -22, gk, ss[28]); // __s28 = __v2 >> 22
    info.eval->rotate_rows(vs[2], -25, gk, ss[29]); // __s29 = __v2 >> 25
    info.eval->rotate_rows(vs[2], -23, gk, ss[30]); // __s30 = __v2 >> 23
    info.eval->rotate_rows(vs[2], -9, gk, ss[31]); // __s31 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -6, gk, ss[32]); // __s32 = __v2 >> 6
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -24, gk, ss[33]); // __s33 = __v3 >> 24
    info.eval->rotate_rows(vs[3], -18, gk, ss[34]); // __s34 = __v3 >> 18
    info.eval->rotate_rows(vs[3], -27, gk, ss[35]); // __s35 = __v3 >> 27
    info.eval->rotate_rows(vs[3], -22, gk, ss[36]); // __s36 = __v3 >> 22
    info.eval->rotate_rows(vs[3], -10, gk, ss[37]); // __s37 = __v3 >> 10
    info.eval->rotate_rows(vs[3], -6, gk, ss[38]); // __s38 = __v3 >> 6
    info.eval->rotate_rows(vs[3], -7, gk, ss[39]); // __s39 = __v3 >> 7
    info.eval->rotate_rows(vs[3], -9, gk, ss[40]); // __s40 = __v3 >> 9
    info.eval->rotate_rows(vs[3], -11, gk, ss[41]); // __s41 = __v3 >> 11
    info.eval->rotate_rows(vs[3], -23, gk, ss[42]); // __s42 = __v3 >> 23
    info.eval->rotate_rows(vs[3], -17, gk, ss[43]); // __s43 = __v3 >> 17
    info.eval->rotate_rows(vs[3], -5, gk, ss[44]); // __s44 = __v3 >> 5
    
    // __t8 = blend(__s12@1000000000000000000000000000, __s6@0000000110000000000000000000, __s7@0000000001100000000000000000, __s2@0000000000001000000001000000, __s8@0000000000000100000000000000, __s11@0000000000000000000100000000, __s9@0000000000000000000000000010)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7;
    info.eval->multiply_plain(ss[12], bits["1000000000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[6], bits["0000000110000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[7], bits["0000000001100000000000000000"], t8_3);
    info.eval->multiply_plain(ss[2], bits["0000000000001000000001000000"], t8_4);
    info.eval->multiply_plain(ss[8], bits["0000000000000100000000000000"], t8_5);
    info.eval->multiply_plain(ss[11], bits["0000000000000000000100000000"], t8_6);
    info.eval->multiply_plain(ss[9], bits["0000000000000000000000000010"], t8_7);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7}, ts[8]);
    
    
    // __t9 = blend(__s36@1000000000000000000000000000, __s22@0000000100000000000001000000, __s26@0000000010000000000000000000, __s28@0000000001000000000000000000, __s30@0000000000100000000000000000, __s29@0000000000001000000000000000, __s23@0000000000000100000000000010, __s40@0000000000000000000100000000)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7, t9_8;
    info.eval->multiply_plain(ss[36], bits["1000000000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[22], bits["0000000100000000000001000000"], t9_2);
    info.eval->multiply_plain(ss[26], bits["0000000010000000000000000000"], t9_3);
    info.eval->multiply_plain(ss[28], bits["0000000001000000000000000000"], t9_4);
    info.eval->multiply_plain(ss[30], bits["0000000000100000000000000000"], t9_5);
    info.eval->multiply_plain(ss[29], bits["0000000000001000000000000000"], t9_6);
    info.eval->multiply_plain(ss[23], bits["0000000000000100000000000010"], t9_7);
    info.eval->multiply_plain(ss[40], bits["0000000000000000000100000000"], t9_8);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7, t9_8}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    
    // __t10 = blend(__s14@0000010000000000000000000000, __s5@0000001000000000000000000000, __s7@0000000001000000000000000000, __s16@0000000000000001000000000000, __s19@0000000000000000010000000000, __s2@0000000000000000000001000000, __s21@0000000000000000000000001000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7;
    info.eval->multiply_plain(ss[14], bits["0000010000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[5], bits["0000001000000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[7], bits["0000000001000000000000000000"], t10_3);
    info.eval->multiply_plain(ss[16], bits["0000000000000001000000000000"], t10_4);
    info.eval->multiply_plain(ss[19], bits["0000000000000000010000000000"], t10_5);
    info.eval->multiply_plain(ss[2], bits["0000000000000000000001000000"], t10_6);
    info.eval->multiply_plain(ss[21], bits["0000000000000000000000001000"], t10_7);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7}, ts[10]);
    
    
    // __t11 = blend(__s35@0000010000000000000000000000, __s28@0000001001000000000000000000, __s44@0000000000000001000000000000, __s37@0000000000000000010000000000, __s22@0000000000000000000001000000, __s34@0000000000000000000000001000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6;
    info.eval->multiply_plain(ss[35], bits["0000010000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[28], bits["0000001001000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[44], bits["0000000000000001000000000000"], t11_3);
    info.eval->multiply_plain(ss[37], bits["0000000000000000010000000000"], t11_4);
    info.eval->multiply_plain(ss[22], bits["0000000000000000000001000000"], t11_5);
    info.eval->multiply_plain(ss[34], bits["0000000000000000000000001000"], t11_6);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__s13@0100000000000000000000000000, __s14@0000100000000000000000000000, __s7@0000000000010000000000000000, __s16@0000000000000000001000000000, __s17@0000000000000000000000000001)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5;
    info.eval->multiply_plain(ss[13], bits["0100000000000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[14], bits["0000100000000000000000000000"], t12_2);
    info.eval->multiply_plain(ss[7], bits["0000000000010000000000000000"], t12_3);
    info.eval->multiply_plain(ss[16], bits["0000000000000000001000000000"], t12_4);
    info.eval->multiply_plain(ss[17], bits["0000000000000000000000000001"], t12_5);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5}, ts[12]);
    
    
    // __t13 = blend(__s36@0100000000000000000000000000, __s42@0000100000000000000000000000, __s27@0000000000010000000000000000, __s40@0000000000000000001000000000, __s43@0000000000000000000000000001)
    ctxt t13_1, t13_2, t13_3, t13_4, t13_5;
    info.eval->multiply_plain(ss[36], bits["0100000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[42], bits["0000100000000000000000000000"], t13_2);
    info.eval->multiply_plain(ss[27], bits["0000000000010000000000000000"], t13_3);
    info.eval->multiply_plain(ss[40], bits["0000000000000000001000000000"], t13_4);
    info.eval->multiply_plain(ss[43], bits["0000000000000000000000000001"], t13_5);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4, t13_5}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    
    // __t14 = blend(__s2@0000000000001000000000000000, __s19@0000000000000000010000000000, __s16@0000000000000000001000000000, __s18@0000000000000000000010000000, __s1@0000000000000000000000100000)
    ctxt t14_1, t14_2, t14_3, t14_4, t14_5;
    info.eval->multiply_plain(ss[2], bits["0000000000001000000000000000"], t14_1);
    info.eval->multiply_plain(ss[19], bits["0000000000000000010000000000"], t14_2);
    info.eval->multiply_plain(ss[16], bits["0000000000000000001000000000"], t14_3);
    info.eval->multiply_plain(ss[18], bits["0000000000000000000010000000"], t14_4);
    info.eval->multiply_plain(ss[1], bits["0000000000000000000000100000"], t14_5);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4, t14_5}, ts[14]);
    
    
    // __t15 = blend(__s29@0000000000001000000000000000, __s37@0000000000000000010000000000, __s40@0000000000000000001000000000, __s41@0000000000000000000010000000, __s32@0000000000000000000000100000)
    ctxt t15_1, t15_2, t15_3, t15_4, t15_5;
    info.eval->multiply_plain(ss[29], bits["0000000000001000000000000000"], t15_1);
    info.eval->multiply_plain(ss[37], bits["0000000000000000010000000000"], t15_2);
    info.eval->multiply_plain(ss[40], bits["0000000000000000001000000000"], t15_3);
    info.eval->multiply_plain(ss[41], bits["0000000000000000000010000000"], t15_4);
    info.eval->multiply_plain(ss[32], bits["0000000000000000000000100000"], t15_5);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4, t15_5}, ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[7]); // __v7 = __t14 + __t15
    
    // __t16 = blend(__s12@1000000000000000000000000000, __s13@0100000000000000000000000000, __s14@0001010000000000000000000000, __s6@0000000010000000000000000000, __s3@0000000000000010000000000000, __s15@0000000000000000100000000000, __s1@0000000000000000000000100000, __s10@0000000000000000000000010000, __s4@0000000000000000000000000100, __s17@0000000000000000000000000001)
    ctxt t16_1, t16_2, t16_3, t16_4, t16_5, t16_6, t16_7, t16_8, t16_9, t16_10;
    info.eval->multiply_plain(ss[12], bits["1000000000000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[13], bits["0100000000000000000000000000"], t16_2);
    info.eval->multiply_plain(ss[14], bits["0001010000000000000000000000"], t16_3);
    info.eval->multiply_plain(ss[6], bits["0000000010000000000000000000"], t16_4);
    info.eval->multiply_plain(ss[3], bits["0000000000000010000000000000"], t16_5);
    info.eval->multiply_plain(ss[15], bits["0000000000000000100000000000"], t16_6);
    info.eval->multiply_plain(ss[1], bits["0000000000000000000000100000"], t16_7);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000000010000"], t16_8);
    info.eval->multiply_plain(ss[4], bits["0000000000000000000000000100"], t16_9);
    info.eval->multiply_plain(ss[17], bits["0000000000000000000000000001"], t16_10);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, t16_5, t16_6, t16_7, t16_8, t16_9, t16_10}, ts[16]);
    
    
    // __t17 = blend(__s36@1101000000000000000000000000, __s35@0000010000000000000000000000, __s26@0000000010000000000000000000, __s24@0000000000000010000000000000, __s38@0000000000000000100000000000, __s32@0000000000000000000000100000, __s25@0000000000000000000000010000, __s31@0000000000000000000000000100, __s43@0000000000000000000000000001)
    ctxt t17_1, t17_2, t17_3, t17_4, t17_5, t17_6, t17_7, t17_8, t17_9;
    info.eval->multiply_plain(ss[36], bits["1101000000000000000000000000"], t17_1);
    info.eval->multiply_plain(ss[35], bits["0000010000000000000000000000"], t17_2);
    info.eval->multiply_plain(ss[26], bits["0000000010000000000000000000"], t17_3);
    info.eval->multiply_plain(ss[24], bits["0000000000000010000000000000"], t17_4);
    info.eval->multiply_plain(ss[38], bits["0000000000000000100000000000"], t17_5);
    info.eval->multiply_plain(ss[32], bits["0000000000000000000000100000"], t17_6);
    info.eval->multiply_plain(ss[25], bits["0000000000000000000000010000"], t17_7);
    info.eval->multiply_plain(ss[31], bits["0000000000000000000000000100"], t17_8);
    info.eval->multiply_plain(ss[43], bits["0000000000000000000000000001"], t17_9);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4, t17_5, t17_6, t17_7, t17_8, t17_9}, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[8]); // __v8 = __t16 + __t17
    
    // __t18 = blend(__v4@1000000001000000000000000000, __v6@0100000000000000000000000000, __v7@0000000000000000010000000000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[4], bits["1000000001000000000000000000"], t18_1);
    info.eval->multiply_plain(vs[6], bits["0100000000000000000000000000"], t18_2);
    info.eval->multiply_plain(vs[7], bits["0000000000000000010000000000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    
    // __t19 = blend(__v8@1100000000000000000000000000, __v5@0000000001000000010000000000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[8], bits["1100000000000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[5], bits["0000000001000000010000000000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[9]); // __v9 = __t18 * __t19
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -22, gk, ss[45]); // __s45 = __v9 >> 22
    
    // __t20 = blend(__s14@0001000000000000000000000000, __s6@0000000100000000000000000000, __s3@0000000000000010000000000000, __s16@0000000000000001000000000000, __s18@0000000000000000000010000000, __s21@0000000000000000000000001000)
    ctxt t20_1, t20_2, t20_3, t20_4, t20_5, t20_6;
    info.eval->multiply_plain(ss[14], bits["0001000000000000000000000000"], t20_1);
    info.eval->multiply_plain(ss[6], bits["0000000100000000000000000000"], t20_2);
    info.eval->multiply_plain(ss[3], bits["0000000000000010000000000000"], t20_3);
    info.eval->multiply_plain(ss[16], bits["0000000000000001000000000000"], t20_4);
    info.eval->multiply_plain(ss[18], bits["0000000000000000000010000000"], t20_5);
    info.eval->multiply_plain(ss[21], bits["0000000000000000000000001000"], t20_6);
    info.eval->add_many({t20_1, t20_2, t20_3, t20_4, t20_5, t20_6}, ts[20]);
    
    
    // __t21 = blend(__s36@0001000000000000000000000000, __s22@0000000100000000000000000000, __s24@0000000000000010000000000000, __s44@0000000000000001000000000000, __s41@0000000000000000000010000000, __s34@0000000000000000000000001000)
    ctxt t21_1, t21_2, t21_3, t21_4, t21_5, t21_6;
    info.eval->multiply_plain(ss[36], bits["0001000000000000000000000000"], t21_1);
    info.eval->multiply_plain(ss[22], bits["0000000100000000000000000000"], t21_2);
    info.eval->multiply_plain(ss[24], bits["0000000000000010000000000000"], t21_3);
    info.eval->multiply_plain(ss[44], bits["0000000000000001000000000000"], t21_4);
    info.eval->multiply_plain(ss[41], bits["0000000000000000000010000000"], t21_5);
    info.eval->multiply_plain(ss[34], bits["0000000000000000000000001000"], t21_6);
    info.eval->add_many({t21_1, t21_2, t21_3, t21_4, t21_5, t21_6}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[10]); // __v10 = __t20 + __t21
    
    // __t22 = blend(__v8@0000000000000010000000000000, __v7@0000000000000000000000100000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[8], bits["0000000000000010000000000000"], t22_1);
    info.eval->multiply_plain(vs[7], bits["0000000000000000000000100000"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);
    
    
    // __t23 = blend(__v10@0000000000000010000000000000, __v8@0000000000000000000000100000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(vs[10], bits["0000000000000010000000000000"], t23_1);
    info.eval->multiply_plain(vs[8], bits["0000000000000000000000100000"], t23_2);
    info.eval->add(t23_1, t23_2, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[11]); // __v11 = __t22 * __t23
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -22, gk, ss[46]); // __s46 = __v11 >> 22
    info.eval->multiply(vs[6], vs[8], vs[12]); // __v12 = __v6 * __v8
    info.eval->relinearize_inplace(vs[12], rk);
    
    // __t24 = blend(__s8@0000000000000100000000000000, __s4@0000000000000000000000000001)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(ss[8], bits["0000000000000100000000000000"], t24_1);
    info.eval->multiply_plain(ss[4], bits["0000000000000000000000000001"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    info.eval->add(ts[24], ss[23], vs[13]); // __v13 = __t24 + __s23
    
    // __t25 = blend(__s5@0000001000000000000000000000, __s4@0000000000000000000000000001)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(ss[5], bits["0000001000000000000000000000"], t25_1);
    info.eval->multiply_plain(ss[4], bits["0000000000000000000000000001"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    
    // __t26 = blend(__s28@0000001000000000000000000000, __s23@0000000000000000000000000001)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(ss[28], bits["0000001000000000000000000000"], t26_1);
    info.eval->multiply_plain(ss[23], bits["0000000000000000000000000001"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    info.eval->add(ts[25], ts[26], vs[14]); // __v14 = __t25 + __t26
    
    // __t27 = blend(__v8@0001000000000000000000000000, __v10@0000000100000000000000000000, __v14@0000000000000000000000000001)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(vs[8], bits["0001000000000000000000000000"], t27_1);
    info.eval->multiply_plain(vs[10], bits["0000000100000000000000000000"], t27_2);
    info.eval->multiply_plain(vs[14], bits["0000000000000000000000000001"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3}, ts[27]);
    
    
    // __t28 = blend(__v10@0001000000000000000000000000, __v4@0000000100000000000000000000, __v13@0000000000000000000000000001)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[10], bits["0001000000000000000000000000"], t28_1);
    info.eval->multiply_plain(vs[4], bits["0000000100000000000000000000"], t28_2);
    info.eval->multiply_plain(vs[13], bits["0000000000000000000000000001"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3}, ts[28]);
    
    info.eval->multiply(ts[27], ts[28], vs[15]); // __v15 = __t27 * __t28
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->rotate_rows(vs[15], -22, gk, ss[47]); // __s47 = __v15 >> 22
    
    // __t29 = blend(__v5@0000010000000000000000000000, __v7@0000000000000000000010000000)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(vs[5], bits["0000010000000000000000000000"], t29_1);
    info.eval->multiply_plain(vs[7], bits["0000000000000000000010000000"], t29_2);
    info.eval->add(t29_1, t29_2, ts[29]);
    
    
    // __t30 = blend(__v8@0000010000000000000000000000, __v10@0000000000000000000010000000)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(vs[8], bits["0000010000000000000000000000"], t30_1);
    info.eval->multiply_plain(vs[10], bits["0000000000000000000010000000"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    info.eval->multiply(ts[29], ts[30], vs[16]); // __v16 = __t29 * __t30
    info.eval->relinearize_inplace(vs[16], rk);
    
    // __t31 = blend(__s11@0000000000000000000100000000, __s10@0000000000000000000000010000)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(ss[11], bits["0000000000000000000100000000"], t31_1);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000000010000"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    
    // __t32 = blend(__s40@0000000000000000000100000000, __s25@0000000000000000000000010000)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(ss[40], bits["0000000000000000000100000000"], t32_1);
    info.eval->multiply_plain(ss[25], bits["0000000000000000000000010000"], t32_2);
    info.eval->add(t32_1, t32_2, ts[32]);
    
    info.eval->add(ts[31], ts[32], vs[17]); // __v17 = __t31 + __t32
    
    // __t33 = blend(__v4@0000000000000100000000000000, __v6@0000000000000000001000000000, __v17@0000000000000000000000010000, __v10@0000000000000000000000001000)
    ctxt t33_1, t33_2, t33_3, t33_4;
    info.eval->multiply_plain(vs[4], bits["0000000000000100000000000000"], t33_1);
    info.eval->multiply_plain(vs[6], bits["0000000000000000001000000000"], t33_2);
    info.eval->multiply_plain(vs[17], bits["0000000000000000000000010000"], t33_3);
    info.eval->multiply_plain(vs[10], bits["0000000000000000000000001000"], t33_4);
    info.eval->add_many({t33_1, t33_2, t33_3, t33_4}, ts[33]);
    
    
    // __t34 = blend(__v13@0000000000000100000000000000, __v7@0000000000000000001000000000, __v8@0000000000000000000000010000, __v5@0000000000000000000000001000)
    ctxt t34_1, t34_2, t34_3, t34_4;
    info.eval->multiply_plain(vs[13], bits["0000000000000100000000000000"], t34_1);
    info.eval->multiply_plain(vs[7], bits["0000000000000000001000000000"], t34_2);
    info.eval->multiply_plain(vs[8], bits["0000000000000000000000010000"], t34_3);
    info.eval->multiply_plain(vs[5], bits["0000000000000000000000001000"], t34_4);
    info.eval->add_many({t34_1, t34_2, t34_3, t34_4}, ts[34]);
    
    info.eval->multiply(ts[33], ts[34], vs[18]); // __v18 = __t33 * __t34
    info.eval->relinearize_inplace(vs[18], rk);
    info.eval->rotate_rows(vs[18], -22, gk, ss[48]); // __s48 = __v18 >> 22
    info.eval->add(ss[15], ss[38], vs[19]); // __v19 = __s15 + __s38
    info.eval->add(ss[4], ss[31], vs[20]); // __v20 = __s4 + __s31
    
    // __t35 = blend(__s13@0010000000000000000000000000, __s14@0000100000000000000000000000, __s15@0000000000000100000000000000, __s20@0000000000000010000000000000, __s0@0000000000000000000000001000)
    ctxt t35_1, t35_2, t35_3, t35_4, t35_5;
    info.eval->multiply_plain(ss[13], bits["0010000000000000000000000000"], t35_1);
    info.eval->multiply_plain(ss[14], bits["0000100000000000000000000000"], t35_2);
    info.eval->multiply_plain(ss[15], bits["0000000000000100000000000000"], t35_3);
    info.eval->multiply_plain(ss[20], bits["0000000000000010000000000000"], t35_4);
    info.eval->multiply_plain(ss[0], bits["0000000000000000000000001000"], t35_5);
    info.eval->add_many({t35_1, t35_2, t35_3, t35_4, t35_5}, ts[35]);
    
    
    // __t36 = blend(__s33@0010000000000000000000000000, __s42@0000100000000000000000000000, __s38@0000000000000100000000000000, __s39@0000000000000010000000000000, __s24@0000000000000000000000001000)
    ctxt t36_1, t36_2, t36_3, t36_4, t36_5;
    info.eval->multiply_plain(ss[33], bits["0010000000000000000000000000"], t36_1);
    info.eval->multiply_plain(ss[42], bits["0000100000000000000000000000"], t36_2);
    info.eval->multiply_plain(ss[38], bits["0000000000000100000000000000"], t36_3);
    info.eval->multiply_plain(ss[39], bits["0000000000000010000000000000"], t36_4);
    info.eval->multiply_plain(ss[24], bits["0000000000000000000000001000"], t36_5);
    info.eval->add_many({t36_1, t36_2, t36_3, t36_4, t36_5}, ts[36]);
    
    info.eval->add(ts[35], ts[36], vs[21]); // __v21 = __t35 + __t36
    
    // __t37 = blend(__s15@0000000000000100000000000000, __s20@0000000000000010000000000000, __s0@0000000000000000000000001000)
    ctxt t37_1, t37_2, t37_3;
    info.eval->multiply_plain(ss[15], bits["0000000000000100000000000000"], t37_1);
    info.eval->multiply_plain(ss[20], bits["0000000000000010000000000000"], t37_2);
    info.eval->multiply_plain(ss[0], bits["0000000000000000000000001000"], t37_3);
    info.eval->add_many({t37_1, t37_2, t37_3}, ts[37]);
    
    
    // __t38 = blend(__s38@0000000000000100000000000000, __s39@0000000000000010000000000000, __s24@0000000000000000000000001000)
    ctxt t38_1, t38_2, t38_3;
    info.eval->multiply_plain(ss[38], bits["0000000000000100000000000000"], t38_1);
    info.eval->multiply_plain(ss[39], bits["0000000000000010000000000000"], t38_2);
    info.eval->multiply_plain(ss[24], bits["0000000000000000000000001000"], t38_3);
    info.eval->add_many({t38_1, t38_2, t38_3}, ts[38]);
    
    info.eval->add(ts[37], ts[38], vs[22]); // __v22 = __t37 + __t38
    
    // __t39 = blend(__v5@0000001000000000000000000000, __v22@0000000000000100000000001000, __v21@0000000000000010000000000000, __v10@0000000000000001000000000000, __v4@0000000000000000000100000000, __v20@0000000000000000000000000100)
    ctxt t39_1, t39_2, t39_3, t39_4, t39_5, t39_6;
    info.eval->multiply_plain(vs[5], bits["0000001000000000000000000000"], t39_1);
    info.eval->multiply_plain(vs[22], bits["0000000000000100000000001000"], t39_2);
    info.eval->multiply_plain(vs[21], bits["0000000000000010000000000000"], t39_3);
    info.eval->multiply_plain(vs[10], bits["0000000000000001000000000000"], t39_4);
    info.eval->multiply_plain(vs[4], bits["0000000000000000000100000000"], t39_5);
    info.eval->multiply_plain(vs[20], bits["0000000000000000000000000100"], t39_6);
    info.eval->add_many({t39_1, t39_2, t39_3, t39_4, t39_5, t39_6}, ts[39]);
    
    
    // __t40 = blend(__v14@0000001000000000000000000000, __v21@0000000000000100000000001000, __v22@0000000000000010000000000000, __v5@0000000000000001000000000000, __v17@0000000000000000000100000000, __v8@0000000000000000000000000100)
    ctxt t40_1, t40_2, t40_3, t40_4, t40_5, t40_6;
    info.eval->multiply_plain(vs[14], bits["0000001000000000000000000000"], t40_1);
    info.eval->multiply_plain(vs[21], bits["0000000000000100000000001000"], t40_2);
    info.eval->multiply_plain(vs[22], bits["0000000000000010000000000000"], t40_3);
    info.eval->multiply_plain(vs[5], bits["0000000000000001000000000000"], t40_4);
    info.eval->multiply_plain(vs[17], bits["0000000000000000000100000000"], t40_5);
    info.eval->multiply_plain(vs[8], bits["0000000000000000000000000100"], t40_6);
    info.eval->add_many({t40_1, t40_2, t40_3, t40_4, t40_5, t40_6}, ts[40]);
    
    info.eval->multiply(ts[39], ts[40], vs[23]); // __v23 = __t39 * __t40
    info.eval->relinearize_inplace(vs[23], rk);
    info.eval->rotate_rows(vs[23], -22, gk, ss[49]); // __s49 = __v23 >> 22
    
    // __t41 = blend(__v18@0000000000000100000000000000, __v11@0000000000000010000000000000, __v23@0000000000000000000000001000, __v15@0000000000000000000000000001)
    ctxt t41_1, t41_2, t41_3, t41_4;
    info.eval->multiply_plain(vs[18], bits["0000000000000100000000000000"], t41_1);
    info.eval->multiply_plain(vs[11], bits["0000000000000010000000000000"], t41_2);
    info.eval->multiply_plain(vs[23], bits["0000000000000000000000001000"], t41_3);
    info.eval->multiply_plain(vs[15], bits["0000000000000000000000000001"], t41_4);
    info.eval->add_many({t41_1, t41_2, t41_3, t41_4}, ts[41]);
    
    
    // __t42 = blend(__v23@0000000000000110000000000000, __v18@0000000000000000000000001000, __v12@0000000000000000000000000001)
    ctxt t42_1, t42_2, t42_3;
    info.eval->multiply_plain(vs[23], bits["0000000000000110000000000000"], t42_1);
    info.eval->multiply_plain(vs[18], bits["0000000000000000000000001000"], t42_2);
    info.eval->multiply_plain(vs[12], bits["0000000000000000000000000001"], t42_3);
    info.eval->add_many({t42_1, t42_2, t42_3}, ts[42]);
    
    info.eval->sub(ts[41], ts[42], vs[24]); // __v24 = __t41 - __t42
    
    // __t43 = blend(__s13@0010000000000000000000000000, __s7@0000000000110000000000000000, __s9@0000000000000000000000000010)
    ctxt t43_1, t43_2, t43_3;
    info.eval->multiply_plain(ss[13], bits["0010000000000000000000000000"], t43_1);
    info.eval->multiply_plain(ss[7], bits["0000000000110000000000000000"], t43_2);
    info.eval->multiply_plain(ss[9], bits["0000000000000000000000000010"], t43_3);
    info.eval->add_many({t43_1, t43_2, t43_3}, ts[43]);
    
    
    // __t44 = blend(__s33@0010000000000000000000000000, __s30@0000000000100000000000000000, __s27@0000000000010000000000000000, __s23@0000000000000000000000000010)
    ctxt t44_1, t44_2, t44_3, t44_4;
    info.eval->multiply_plain(ss[33], bits["0010000000000000000000000000"], t44_1);
    info.eval->multiply_plain(ss[30], bits["0000000000100000000000000000"], t44_2);
    info.eval->multiply_plain(ss[27], bits["0000000000010000000000000000"], t44_3);
    info.eval->multiply_plain(ss[23], bits["0000000000000000000000000010"], t44_4);
    info.eval->add_many({t44_1, t44_2, t44_3, t44_4}, ts[44]);
    
    info.eval->add(ts[43], ts[44], vs[25]); // __v25 = __t43 + __t44
    
    // __t45 = blend(__v25@0010000000000000000000000000, __v6@0000000000010000000000000000)
    ctxt t45_1, t45_2;
    info.eval->multiply_plain(vs[25], bits["0010000000000000000000000000"], t45_1);
    info.eval->multiply_plain(vs[6], bits["0000000000010000000000000000"], t45_2);
    info.eval->add(t45_1, t45_2, ts[45]);
    
    
    // __t46 = blend(__v21@0010000000000000000000000000, __v25@0000000000010000000000000000)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(vs[21], bits["0010000000000000000000000000"], t46_1);
    info.eval->multiply_plain(vs[25], bits["0000000000010000000000000000"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    info.eval->multiply(ts[45], ts[46], vs[26]); // __v26 = __t45 * __t46
    info.eval->relinearize_inplace(vs[26], rk);
    info.eval->rotate_rows(vs[26], -22, gk, ss[50]); // __s50 = __v26 >> 22
    
    // __t47 = blend(__v5@0000000000000000000001000000, __v25@0000000000000000000000000010)
    ctxt t47_1, t47_2;
    info.eval->multiply_plain(vs[5], bits["0000000000000000000001000000"], t47_1);
    info.eval->multiply_plain(vs[25], bits["0000000000000000000000000010"], t47_2);
    info.eval->add(t47_1, t47_2, ts[47]);
    
    info.eval->multiply(vs[4], ts[47], vs[27]); // __v27 = __v4 * __t47
    info.eval->relinearize_inplace(vs[27], rk);
    info.eval->rotate_rows(vs[27], -22, gk, ss[51]); // __s51 = __v27 >> 22
    
    // __t48 = blend(__v8@0000000010000000000000000000, __v7@0000000000001000000000000000)
    ctxt t48_1, t48_2;
    info.eval->multiply_plain(vs[8], bits["0000000010000000000000000000"], t48_1);
    info.eval->multiply_plain(vs[7], bits["0000000000001000000000000000"], t48_2);
    info.eval->add(t48_1, t48_2, ts[48]);
    
    info.eval->multiply(ts[48], vs[4], vs[28]); // __v28 = __t48 * __v4
    info.eval->relinearize_inplace(vs[28], rk);
    info.eval->rotate_rows(vs[28], -22, gk, ss[52]); // __s52 = __v28 >> 22
    
    // __t49 = blend(__v6@0000100000000000000000000000, __v4@0000000000100000000000000000, __v8@0000000000000000100000000000)
    ctxt t49_1, t49_2, t49_3;
    info.eval->multiply_plain(vs[6], bits["0000100000000000000000000000"], t49_1);
    info.eval->multiply_plain(vs[4], bits["0000000000100000000000000000"], t49_2);
    info.eval->multiply_plain(vs[8], bits["0000000000000000100000000000"], t49_3);
    info.eval->add_many({t49_1, t49_2, t49_3}, ts[49]);
    
    
    // __t50 = blend(__v21@0000100000000000000000000000, __v25@0000000000100000000000000000, __v19@0000000000000000100000000000)
    ctxt t50_1, t50_2, t50_3;
    info.eval->multiply_plain(vs[21], bits["0000100000000000000000000000"], t50_1);
    info.eval->multiply_plain(vs[25], bits["0000000000100000000000000000"], t50_2);
    info.eval->multiply_plain(vs[19], bits["0000000000000000100000000000"], t50_3);
    info.eval->add_many({t50_1, t50_2, t50_3}, ts[50]);
    
    info.eval->multiply(ts[49], ts[50], vs[29]); // __v29 = __t49 * __t50
    info.eval->relinearize_inplace(vs[29], rk);
    info.eval->rotate_rows(vs[29], -22, gk, ss[53]); // __s53 = __v29 >> 22
    info.eval->sub(ss[50], vs[16], vs[30]); // __v30 = __s50 - __v16
    info.eval->sub(vs[28], ss[48], vs[31]); // __v31 = __v28 - __s48
    info.eval->sub(ss[51], vs[16], vs[32]); // __v32 = __s51 - __v16
    info.eval->sub(ss[52], vs[26], vs[33]); // __v33 = __s52 - __v26
    info.eval->sub(ss[46], vs[29], vs[34]); // __v34 = __s46 - __v29
    info.eval->sub(ss[49], vs[9], vs[35]); // __v35 = __s49 - __v9
    info.eval->sub(ss[48], vs[9], vs[36]); // __v36 = __s48 - __v9
    info.eval->sub(ss[53], vs[29], vs[37]); // __v37 = __s53 - __v29
    info.eval->sub(ss[45], vs[15], vs[38]); // __v38 = __s45 - __v15
    info.eval->sub(ss[47], vs[9], vs[39]); // __v39 = __s47 - __v9
    info.eval->sub(ss[51], vs[23], vs[40]); // __v40 = __s51 - __v23
    info.eval->sub(ss[49], vs[23], vs[41]); // __v41 = __s49 - __v23
    return vs[41];
}
    