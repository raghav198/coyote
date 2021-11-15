
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000000000001000000000010", info);
    add_bitstring(bits, "0000010000000000000000000000", info);
    add_bitstring(bits, "0000000000000000100000000001", info);
    add_bitstring(bits, "0000000001000000000000000000", info);
    add_bitstring(bits, "0000000000000000001000001000", info);
    add_bitstring(bits, "0000000000000000000000000001", info);
    add_bitstring(bits, "0000000000000000000000000100", info);
    add_bitstring(bits, "0000000000000000000000001000", info);
    add_bitstring(bits, "0000000100000000000000000000", info);
    add_bitstring(bits, "1000000000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000001001000", info);
    add_bitstring(bits, "0001000000000000000000000000", info);
    add_bitstring(bits, "0000000000001000000000000000", info);
    add_bitstring(bits, "0010000000000000000000000000", info);
    add_bitstring(bits, "0000100000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000010000000", info);
    add_bitstring(bits, "0100000000000000000000000000", info);
    add_bitstring(bits, "0000000000100000000000000000", info);
    add_bitstring(bits, "0000000000000001000000000000", info);
    add_bitstring(bits, "0000000000000000001000000000", info);
    add_bitstring(bits, "0000000000000100000000010000", info);
    add_bitstring(bits, "0000010000000000000000010000", info);
    add_bitstring(bits, "0000000000000010000000000000", info);
    add_bitstring(bits, "0000000000000000000000010000", info);
    add_bitstring(bits, "0000001000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000000000010", info);
    add_bitstring(bits, "0000000000000000100000000000", info);
    add_bitstring(bits, "0000000000000100000000000000", info);
    add_bitstring(bits, "0000000000010000000000000000", info);
    add_bitstring(bits, "0000000000000000010000000000", info);
    add_bitstring(bits, "0000000000000000000001000000", info);
    add_bitstring(bits, "0000000000000000000000100000", info);
    add_bitstring(bits, "0000000010000000000000000000", info);
    add_bitstring(bits, "0000000000000000000100000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(66);
    ts[0] = encrypt_input("000000000001111110110000000000111000", info);
    ts[2] = encrypt_input("000000000001111110011000000000011100", info);
    ts[4] = encrypt_input("000000011100011111100000110000000000", info);
    ts[6] = encrypt_input("000000001110001111110000000000000110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[45];
    ctxt ss[65];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -27, gk, ss[0]); // __s0 = __v0 >> 27
    info.eval->rotate_rows(vs[0], -17, gk, ss[1]); // __s1 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -3, gk, ss[2]); // __s2 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -5, gk, ss[3]); // __s3 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -20, gk, ss[4]); // __s4 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -23, gk, ss[5]); // __s5 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -13, gk, ss[6]); // __s6 = __v0 >> 13
    info.eval->rotate_rows(vs[0], -15, gk, ss[7]); // __s7 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -8, gk, ss[8]); // __s8 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -16, gk, ss[9]); // __s9 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -12, gk, ss[10]); // __s10 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -22, gk, ss[11]); // __s11 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -24, gk, ss[12]); // __s12 = __v0 >> 24
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -16, gk, ss[13]); // __s13 = __v1 >> 16
    info.eval->rotate_rows(vs[1], -22, gk, ss[14]); // __s14 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -14, gk, ss[15]); // __s15 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -23, gk, ss[16]); // __s16 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -27, gk, ss[17]); // __s17 = __v1 >> 27
    info.eval->rotate_rows(vs[1], -17, gk, ss[18]); // __s18 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -3, gk, ss[19]); // __s19 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -5, gk, ss[20]); // __s20 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -8, gk, ss[21]); // __s21 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -11, gk, ss[22]); // __s22 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -24, gk, ss[23]); // __s23 = __v1 >> 24
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -3, gk, ss[24]); // __s24 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -20, gk, ss[25]); // __s25 = __v2 >> 20
    info.eval->rotate_rows(vs[2], -13, gk, ss[26]); // __s26 = __v2 >> 13
    info.eval->rotate_rows(vs[2], -23, gk, ss[27]); // __s27 = __v2 >> 23
    info.eval->rotate_rows(vs[2], -24, gk, ss[28]); // __s28 = __v2 >> 24
    info.eval->rotate_rows(vs[2], -25, gk, ss[29]); // __s29 = __v2 >> 25
    info.eval->rotate_rows(vs[2], -5, gk, ss[30]); // __s30 = __v2 >> 5
    info.eval->rotate_rows(vs[2], -1, gk, ss[31]); // __s31 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -16, gk, ss[32]); // __s32 = __v2 >> 16
    info.eval->rotate_rows(vs[2], -14, gk, ss[33]); // __s33 = __v2 >> 14
    info.eval->rotate_rows(vs[2], -6, gk, ss[34]); // __s34 = __v2 >> 6
    info.eval->rotate_rows(vs[2], -4, gk, ss[35]); // __s35 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -7, gk, ss[36]); // __s36 = __v2 >> 7
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -3, gk, ss[37]); // __s37 = __v3 >> 3
    info.eval->rotate_rows(vs[3], -19, gk, ss[38]); // __s38 = __v3 >> 19
    info.eval->rotate_rows(vs[3], -13, gk, ss[39]); // __s39 = __v3 >> 13
    info.eval->rotate_rows(vs[3], -23, gk, ss[40]); // __s40 = __v3 >> 23
    info.eval->rotate_rows(vs[3], -25, gk, ss[41]); // __s41 = __v3 >> 25
    info.eval->rotate_rows(vs[3], -5, gk, ss[42]); // __s42 = __v3 >> 5
    info.eval->rotate_rows(vs[3], -22, gk, ss[43]); // __s43 = __v3 >> 22
    info.eval->rotate_rows(vs[3], -1, gk, ss[44]); // __s44 = __v3 >> 1
    info.eval->rotate_rows(vs[3], -16, gk, ss[45]); // __s45 = __v3 >> 16
    info.eval->rotate_rows(vs[3], -20, gk, ss[46]); // __s46 = __v3 >> 20
    info.eval->rotate_rows(vs[3], -6, gk, ss[47]); // __s47 = __v3 >> 6
    info.eval->rotate_rows(vs[3], -24, gk, ss[48]); // __s48 = __v3 >> 24
    info.eval->rotate_rows(vs[3], -26, gk, ss[49]); // __s49 = __v3 >> 26
    
    // __t8 = blend(__s5@0000000100000000000000000000, __s14@0000000001000000000000000000, __s0@0000000000100000000000000000, __s20@0000000000000000010000000000, __s11@0000000000000000001000000000, __s15@0000000000000000000000000100)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6;
    info.eval->multiply_plain(ss[5], bits["0000000100000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[14], bits["0000000001000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[0], bits["0000000000100000000000000000"], t8_3);
    info.eval->multiply_plain(ss[20], bits["0000000000000000010000000000"], t8_4);
    info.eval->multiply_plain(ss[11], bits["0000000000000000001000000000"], t8_5);
    info.eval->multiply_plain(ss[15], bits["0000000000000000000000000100"], t8_6);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6}, ts[8]);
    
    
    // __t9 = blend(__s28@0000000100000000000000000000, __s41@0000000001000000000000000000, __s24@0000000000100000000000000000, __s42@0000000000000000010000000000, __s34@0000000000000000001000000000, __s49@0000000000000000000000000100)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6;
    info.eval->multiply_plain(ss[28], bits["0000000100000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[41], bits["0000000001000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[24], bits["0000000000100000000000000000"], t9_3);
    info.eval->multiply_plain(ss[42], bits["0000000000000000010000000000"], t9_4);
    info.eval->multiply_plain(ss[34], bits["0000000000000000001000000000"], t9_5);
    info.eval->multiply_plain(ss[49], bits["0000000000000000000000000100"], t9_6);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__s14@0000010000000000000000000000, __s16@0000001000000000000000000000, __s5@0000000100000000000000000000, __s17@0000000000010000000000000000, __s11@0000000000000000001000000000, __v0@0000000000000000000000001000, __s6@0000000000000000000000000100)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7;
    info.eval->multiply_plain(ss[14], bits["0000010000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[16], bits["0000001000000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[5], bits["0000000100000000000000000000"], t10_3);
    info.eval->multiply_plain(ss[17], bits["0000000000010000000000000000"], t10_4);
    info.eval->multiply_plain(ss[11], bits["0000000000000000001000000000"], t10_5);
    info.eval->multiply_plain(vs[0], bits["0000000000000000000000001000"], t10_6);
    info.eval->multiply_plain(ss[6], bits["0000000000000000000000000100"], t10_7);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7}, ts[10]);
    
    
    // __t11 = blend(__s46@0000010000000000000000000000, __s43@0000001000000000000000000000, __s28@0000000100000000000000000000, __s37@0000000000010000000000000000, __s34@0000000000000000001000001000, __s36@0000000000000000000000000100)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6;
    info.eval->multiply_plain(ss[46], bits["0000010000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[43], bits["0000001000000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[28], bits["0000000100000000000000000000"], t11_3);
    info.eval->multiply_plain(ss[37], bits["0000000000010000000000000000"], t11_4);
    info.eval->multiply_plain(ss[34], bits["0000000000000000001000001000"], t11_5);
    info.eval->multiply_plain(ss[36], bits["0000000000000000000000000100"], t11_6);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6}, ts[11]);
    
    info.eval->sub(ts[00], ts[01], vs[5]); // __v5 = __t00 - __t01
    
    // __t12 = blend(__s4@0000100000000000000000000000, __s0@0000000000100000000000000000, __s17@0000000000010000000000000000, __s9@0000000000001000000000000000, __s15@0000000000000000000000000100, __s10@0000000000000000000000000010)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5, t12_6;
    info.eval->multiply_plain(ss[4], bits["0000100000000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[0], bits["0000000000100000000000000000"], t12_2);
    info.eval->multiply_plain(ss[17], bits["0000000000010000000000000000"], t12_3);
    info.eval->multiply_plain(ss[9], bits["0000000000001000000000000000"], t12_4);
    info.eval->multiply_plain(ss[15], bits["0000000000000000000000000100"], t12_5);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000000000010"], t12_6);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5, t12_6}, ts[12]);
    
    
    // __t13 = blend(__s25@0000100000000000000000000000, __s24@0000000000100000000000000000, __s37@0000000000010000000000000000, __s31@0000000000001000000000000000, __s49@0000000000000000000000000100, __s33@0000000000000000000000000010)
    ctxt t13_1, t13_2, t13_3, t13_4, t13_5, t13_6;
    info.eval->multiply_plain(ss[25], bits["0000100000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[24], bits["0000000000100000000000000000"], t13_2);
    info.eval->multiply_plain(ss[37], bits["0000000000010000000000000000"], t13_3);
    info.eval->multiply_plain(ss[31], bits["0000000000001000000000000000"], t13_4);
    info.eval->multiply_plain(ss[49], bits["0000000000000000000000000100"], t13_5);
    info.eval->multiply_plain(ss[33], bits["0000000000000000000000000010"], t13_6);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4, t13_5, t13_6}, ts[13]);
    
    info.eval->sub(ts[02], ts[03], vs[6]); // __v6 = __t02 - __t03
    
    // __t14 = blend(__v4@0000000100000000000000000000, __v5@0000000000010000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[4], bits["0000000100000000000000000000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["0000000000010000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v5@0000000100000000000000000000, __v6@0000000000010000000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[5], bits["0000000100000000000000000000"], t15_1);
    info.eval->multiply_plain(vs[6], bits["0000000000010000000000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[04], ts[05], vs[7]); // __v7 = __t04 * __t05
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -4, gk, ss[50]); // __s50 = __v7 >> 4
    
    // __t16 = blend(__s3@0000000000000000100000000000, __s13@0000000000000000000000000001)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(ss[3], bits["0000000000000000100000000000"], t16_1);
    info.eval->multiply_plain(ss[13], bits["0000000000000000000000000001"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__s30@0000000000000000100000000000, __s38@0000000000000000000000000001)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[30], bits["0000000000000000100000000000"], t17_1);
    info.eval->multiply_plain(ss[38], bits["0000000000000000000000000001"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->sub(ts[06], ts[07], vs[8]); // __v8 = __t06 - __t07
    
    // __t18 = blend(__s14@0000000001000000000000000000, __s19@0000000000000001000000000000, __s20@0000000000000000010000000000, __s22@0000000000000000000000000010)
    ctxt t18_1, t18_2, t18_3, t18_4;
    info.eval->multiply_plain(ss[14], bits["0000000001000000000000000000"], t18_1);
    info.eval->multiply_plain(ss[19], bits["0000000000000001000000000000"], t18_2);
    info.eval->multiply_plain(ss[20], bits["0000000000000000010000000000"], t18_3);
    info.eval->multiply_plain(ss[22], bits["0000000000000000000000000010"], t18_4);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4}, ts[18]);
    
    
    // __t19 = blend(__s41@0000000001000000000000000000, __s45@0000000000000001000000000000, __s42@0000000000000000010000000000, __s39@0000000000000000000000000010)
    ctxt t19_1, t19_2, t19_3, t19_4;
    info.eval->multiply_plain(ss[41], bits["0000000001000000000000000000"], t19_1);
    info.eval->multiply_plain(ss[45], bits["0000000000000001000000000000"], t19_2);
    info.eval->multiply_plain(ss[42], bits["0000000000000000010000000000"], t19_3);
    info.eval->multiply_plain(ss[39], bits["0000000000000000000000000010"], t19_4);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4}, ts[19]);
    
    info.eval->sub(ts[08], ts[09], vs[9]); // __v9 = __t08 - __t09
    info.eval->multiply(vs[9], vs[4], vs[10]); // __v10 = __v9 * __v4
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -4, gk, ss[51]); // __s51 = __v10 >> 4
    
    // __t20 = blend(__v6@0000000000100000000000000000, __v4@0000000000000000001000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[6], bits["0000000000100000000000000000"], t20_1);
    info.eval->multiply_plain(vs[4], bits["0000000000000000001000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v4@0000000000100000000000000000, __v5@0000000000000000001000000000)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[4], bits["0000000000100000000000000000"], t21_1);
    info.eval->multiply_plain(vs[5], bits["0000000000000000001000000000"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->multiply(ts[20], ts[21], vs[11]); // __v11 = __t20 * __t21
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -5, gk, ss[52]); // __s52 = __v11 >> 5
    
    // __t22 = blend(__s16@0000001000000000000000000000, __s12@0000000000000000000010000000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(ss[16], bits["0000001000000000000000000000"], t22_1);
    info.eval->multiply_plain(ss[12], bits["0000000000000000000010000000"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);
    
    
    // __t23 = blend(__s43@0000001000000000000000000000, __s26@0000000000000000000010000000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(ss[43], bits["0000001000000000000000000000"], t23_1);
    info.eval->multiply_plain(ss[26], bits["0000000000000000000010000000"], t23_2);
    info.eval->add(t23_1, t23_2, ts[23]);
    
    info.eval->sub(ts[22], ts[23], vs[12]); // __v12 = __t22 - __t23
    
    // __t24 = blend(__s18@0100000000000000000000000000, __s17@0000000000000000000000001000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(ss[18], bits["0100000000000000000000000000"], t24_1);
    info.eval->multiply_plain(ss[17], bits["0000000000000000000000001000"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    
    // __t25 = blend(__s45@0100000000000000000000000000, __s41@0000000000000000000000001000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(ss[45], bits["0100000000000000000000000000"], t25_1);
    info.eval->multiply_plain(ss[41], bits["0000000000000000000000001000"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    info.eval->sub(ts[24], ts[25], vs[13]); // __v13 = __t24 - __t25
    
    // __t26 = blend(__s11@0000000010000000000000000000, __s19@0000000000000001000000000000, __s12@0000000000000000000010000000)
    ctxt t26_1, t26_2, t26_3;
    info.eval->multiply_plain(ss[11], bits["0000000010000000000000000000"], t26_1);
    info.eval->multiply_plain(ss[19], bits["0000000000000001000000000000"], t26_2);
    info.eval->multiply_plain(ss[12], bits["0000000000000000000010000000"], t26_3);
    info.eval->add_many({t26_1, t26_2, t26_3}, ts[26]);
    
    
    // __t27 = blend(__s29@0000000010000000000000000000, __s45@0000000000000001000000000000, __s26@0000000000000000000010000000)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(ss[29], bits["0000000010000000000000000000"], t27_1);
    info.eval->multiply_plain(ss[45], bits["0000000000000001000000000000"], t27_2);
    info.eval->multiply_plain(ss[26], bits["0000000000000000000010000000"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3}, ts[27]);
    
    info.eval->sub(ts[26], ts[27], vs[14]); // __v14 = __t26 - __t27
    
    // __t28 = blend(__s1@1000000000000000000000000000, __s14@0000010000000000000000000000, __s23@0000000000000000000001000000, __s10@0000000000000000000000000010)
    ctxt t28_1, t28_2, t28_3, t28_4;
    info.eval->multiply_plain(ss[1], bits["1000000000000000000000000000"], t28_1);
    info.eval->multiply_plain(ss[14], bits["0000010000000000000000000000"], t28_2);
    info.eval->multiply_plain(ss[23], bits["0000000000000000000001000000"], t28_3);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000000000010"], t28_4);
    info.eval->add_many({t28_1, t28_2, t28_3, t28_4}, ts[28]);
    
    
    // __t29 = blend(__s32@1000000000000000000000000000, __s46@0000010000000000000000000000, __s39@0000000000000000000001000000, __s33@0000000000000000000000000010)
    ctxt t29_1, t29_2, t29_3, t29_4;
    info.eval->multiply_plain(ss[32], bits["1000000000000000000000000000"], t29_1);
    info.eval->multiply_plain(ss[46], bits["0000010000000000000000000000"], t29_2);
    info.eval->multiply_plain(ss[39], bits["0000000000000000000001000000"], t29_3);
    info.eval->multiply_plain(ss[33], bits["0000000000000000000000000010"], t29_4);
    info.eval->add_many({t29_1, t29_2, t29_3, t29_4}, ts[29]);
    
    info.eval->sub(ts[28], ts[29], vs[15]); // __v15 = __t28 - __t29
    
    // __t30 = blend(__s14@0000000000000000000100000000, __s8@0000000000000000000000100000)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(ss[14], bits["0000000000000000000100000000"], t30_1);
    info.eval->multiply_plain(ss[8], bits["0000000000000000000000100000"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    
    // __t31 = blend(__s47@0000000000000000000100000000, __s35@0000000000000000000000100000)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(ss[47], bits["0000000000000000000100000000"], t31_1);
    info.eval->multiply_plain(ss[35], bits["0000000000000000000000100000"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->sub(ts[20], ts[21], vs[16]); // __v16 = __t20 - __t21
    
    // __t32 = blend(__v5@0000001000000000000000000000, __v15@0000000000000000000000000010)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(vs[5], bits["0000001000000000000000000000"], t32_1);
    info.eval->multiply_plain(vs[15], bits["0000000000000000000000000010"], t32_2);
    info.eval->add(t32_1, t32_2, ts[32]);
    
    
    // __t33 = blend(__v12@0000001000000000000000000000, __v6@0000000000000000000000000010)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(vs[12], bits["0000001000000000000000000000"], t33_1);
    info.eval->multiply_plain(vs[6], bits["0000000000000000000000000010"], t33_2);
    info.eval->add(t33_1, t33_2, ts[33]);
    
    info.eval->multiply(ts[22], ts[23], vs[17]); // __v17 = __t22 * __t23
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->rotate_rows(vs[17], -5, gk, ss[53]); // __s53 = __v17 >> 5
    
    // __t34 = blend(__s4@0000100000000000000000000000, __s2@0000000000000010000000000000, __s21@0000000000000000000000010000)
    ctxt t34_1, t34_2, t34_3;
    info.eval->multiply_plain(ss[4], bits["0000100000000000000000000000"], t34_1);
    info.eval->multiply_plain(ss[2], bits["0000000000000010000000000000"], t34_2);
    info.eval->multiply_plain(ss[21], bits["0000000000000000000000010000"], t34_3);
    info.eval->add_many({t34_1, t34_2, t34_3}, ts[34]);
    
    
    // __t35 = blend(__s25@0000100000000000000000000000, __s28@0000000000000010000000000000, __s48@0000000000000000000000010000)
    ctxt t35_1, t35_2, t35_3;
    info.eval->multiply_plain(ss[25], bits["0000100000000000000000000000"], t35_1);
    info.eval->multiply_plain(ss[28], bits["0000000000000010000000000000"], t35_2);
    info.eval->multiply_plain(ss[48], bits["0000000000000000000000010000"], t35_3);
    info.eval->add_many({t35_1, t35_2, t35_3}, ts[35]);
    
    info.eval->sub(ss[9], ss[27], vs[19]); // __v19 = __s9 - __s27
    info.eval->sub(ss[11], ss[29], vs[20]); // __v20 = __s11 - __s29
    
    // __t36 = blend(__s13@0000000000000100000000000000, __s23@0000000000000000000001000000, __v0@0000000000000000000000001000)
    ctxt t36_1, t36_2, t36_3;
    info.eval->multiply_plain(ss[13], bits["0000000000000100000000000000"], t36_1);
    info.eval->multiply_plain(ss[23], bits["0000000000000000000001000000"], t36_2);
    info.eval->multiply_plain(vs[0], bits["0000000000000000000000001000"], t36_3);
    info.eval->add_many({t36_1, t36_2, t36_3}, ts[36]);
    
    
    // __t37 = blend(__s44@0000000000000100000000000000, __s39@0000000000000000000001000000, __s34@0000000000000000000000001000)
    ctxt t37_1, t37_2, t37_3;
    info.eval->multiply_plain(ss[44], bits["0000000000000100000000000000"], t37_1);
    info.eval->multiply_plain(ss[39], bits["0000000000000000000001000000"], t37_2);
    info.eval->multiply_plain(ss[34], bits["0000000000000000000000001000"], t37_3);
    info.eval->add_many({t37_1, t37_2, t37_3}, ts[37]);
    
    
    // __t38 = blend(__v20@0000000010000000000000000000, __v14@0000000000000000000001001000)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(vs[20], bits["0000000010000000000000000000"], t38_1);
    info.eval->multiply_plain(vs[14], bits["0000000000000000000001001000"], t38_2);
    info.eval->add(t38_1, t38_2, ts[38]);
    
    
    // __t39 = blend(__v14@0000000010000000000000000000, __v15@0000000000000000000001000000, __v5@0000000000000000000000001000)
    ctxt t39_1, t39_2, t39_3;
    info.eval->multiply_plain(vs[14], bits["0000000010000000000000000000"], t39_1);
    info.eval->multiply_plain(vs[15], bits["0000000000000000000001000000"], t39_2);
    info.eval->multiply_plain(vs[5], bits["0000000000000000000000001000"], t39_3);
    info.eval->add_many({t39_1, t39_2, t39_3}, ts[39]);
    
    info.eval->multiply(ts[28], ts[29], vs[22]); // __v22 = __t28 * __t29
    info.eval->relinearize_inplace(vs[22], rk);
    info.eval->rotate_rows(vs[22], -5, gk, ss[54]); // __s54 = __v22 >> 5
    info.eval->rotate_rows(vs[22], -4, gk, ss[55]); // __s55 = __v22 >> 4
    
    // __t40 = blend(__s18@0100000000000000000000000000, __s13@0000000000000000000000000001)
    ctxt t40_1, t40_2;
    info.eval->multiply_plain(ss[18], bits["0100000000000000000000000000"], t40_1);
    info.eval->multiply_plain(ss[13], bits["0000000000000000000000000001"], t40_2);
    info.eval->add(t40_1, t40_2, ts[40]);
    
    
    // __t41 = blend(__s45@0100000000000000000000000000, __s38@0000000000000000000000000001)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(ss[45], bits["0100000000000000000000000000"], t41_1);
    info.eval->multiply_plain(ss[38], bits["0000000000000000000000000001"], t41_2);
    info.eval->add(t41_1, t41_2, ts[41]);
    
    info.eval->sub(ts[40], ts[41], vs[23]); // __v23 = __t40 - __t41
    
    // __t42 = blend(__s13@0001000000000000000000000000, __s17@0000000000000000000000001000, __s7@0000000000000000000000000001)
    ctxt t42_1, t42_2, t42_3;
    info.eval->multiply_plain(ss[13], bits["0001000000000000000000000000"], t42_1);
    info.eval->multiply_plain(ss[17], bits["0000000000000000000000001000"], t42_2);
    info.eval->multiply_plain(ss[7], bits["0000000000000000000000000001"], t42_3);
    info.eval->add_many({t42_1, t42_2, t42_3}, ts[42]);
    
    
    // __t43 = blend(__s40@0001000000000000000000000000, __s41@0000000000000000000000001000, __s25@0000000000000000000000000001)
    ctxt t43_1, t43_2, t43_3;
    info.eval->multiply_plain(ss[40], bits["0001000000000000000000000000"], t43_1);
    info.eval->multiply_plain(ss[41], bits["0000000000000000000000001000"], t43_2);
    info.eval->multiply_plain(ss[25], bits["0000000000000000000000000001"], t43_3);
    info.eval->add_many({t43_1, t43_2, t43_3}, ts[43]);
    
    info.eval->sub(ts[42], ts[43], vs[24]); // __v24 = __t42 - __t43
    info.eval->multiply(vs[13], vs[24], vs[25]); // __v25 = __v13 * __v24
    info.eval->relinearize_inplace(vs[25], rk);
    
    // __t44 = blend(__s9@0010000000000000000000000000, __s2@0000000000000010000000000000, __s14@0000000000000000000100000000, __s8@0000000000000000000000100000, __s6@0000000000000000000000000100)
    ctxt t44_1, t44_2, t44_3, t44_4, t44_5;
    info.eval->multiply_plain(ss[9], bits["0010000000000000000000000000"], t44_1);
    info.eval->multiply_plain(ss[2], bits["0000000000000010000000000000"], t44_2);
    info.eval->multiply_plain(ss[14], bits["0000000000000000000100000000"], t44_3);
    info.eval->multiply_plain(ss[8], bits["0000000000000000000000100000"], t44_4);
    info.eval->multiply_plain(ss[6], bits["0000000000000000000000000100"], t44_5);
    info.eval->add_many({t44_1, t44_2, t44_3, t44_4, t44_5}, ts[44]);
    
    
    // __t45 = blend(__s27@0010000000000000000000000000, __s28@0000000000000010000000000000, __s47@0000000000000000000100000000, __s35@0000000000000000000000100000, __s36@0000000000000000000000000100)
    ctxt t45_1, t45_2, t45_3, t45_4, t45_5;
    info.eval->multiply_plain(ss[27], bits["0010000000000000000000000000"], t45_1);
    info.eval->multiply_plain(ss[28], bits["0000000000000010000000000000"], t45_2);
    info.eval->multiply_plain(ss[47], bits["0000000000000000000100000000"], t45_3);
    info.eval->multiply_plain(ss[35], bits["0000000000000000000000100000"], t45_4);
    info.eval->multiply_plain(ss[36], bits["0000000000000000000000000100"], t45_5);
    info.eval->add_many({t45_1, t45_2, t45_3, t45_4, t45_5}, ts[45]);
    
    info.eval->sub(ts[44], ts[45], vs[26]); // __v26 = __t44 - __t45
    
    // __t46 = blend(__v16@0000000000000000000000100000, __v8@0000000000000000000000000001)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(vs[16], bits["0000000000000000000000100000"], t46_1);
    info.eval->multiply_plain(vs[8], bits["0000000000000000000000000001"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    
    // __t47 = blend(__v26@0000000000000000000000100000, __v23@0000000000000000000000000001)
    ctxt t47_1, t47_2;
    info.eval->multiply_plain(vs[26], bits["0000000000000000000000100000"], t47_1);
    info.eval->multiply_plain(vs[23], bits["0000000000000000000000000001"], t47_2);
    info.eval->add(t47_1, t47_2, ts[47]);
    
    info.eval->multiply(ts[46], ts[47], vs[27]); // __v27 = __t46 * __t47
    info.eval->relinearize_inplace(vs[27], rk);
    info.eval->rotate_rows(vs[27], -5, gk, ss[56]); // __s56 = __v27 >> 5
    
    // __t48 = blend(__v26@0010000000000000000000000000, __v15@0000010000000000000000000000, __v13@0000000000000010000000000000)
    ctxt t48_1, t48_2, t48_3;
    info.eval->multiply_plain(vs[26], bits["0010000000000000000000000000"], t48_1);
    info.eval->multiply_plain(vs[15], bits["0000010000000000000000000000"], t48_2);
    info.eval->multiply_plain(vs[13], bits["0000000000000010000000000000"], t48_3);
    info.eval->add_many({t48_1, t48_2, t48_3}, ts[48]);
    
    
    // __t49 = blend(__v19@0010000000000000000000000000, __v5@0000010000000000000000000000, __v26@0000000000000010000000000000)
    ctxt t49_1, t49_2, t49_3;
    info.eval->multiply_plain(vs[19], bits["0010000000000000000000000000"], t49_1);
    info.eval->multiply_plain(vs[5], bits["0000010000000000000000000000"], t49_2);
    info.eval->multiply_plain(vs[26], bits["0000000000000010000000000000"], t49_3);
    info.eval->add_many({t49_1, t49_2, t49_3}, ts[49]);
    
    info.eval->multiply(ts[48], ts[49], vs[28]); // __v28 = __t48 * __t49
    info.eval->relinearize_inplace(vs[28], rk);
    info.eval->rotate_rows(vs[28], -5, gk, ss[57]); // __s57 = __v28 >> 5
    info.eval->rotate_rows(vs[28], -4, gk, ss[58]); // __s58 = __v28 >> 4
    
    // __t50 = blend(__s1@1000000000000000000000000000, __s13@0001000000000000000000000000, __s22@0000000000000000000000000010)
    ctxt t50_1, t50_2, t50_3;
    info.eval->multiply_plain(ss[1], bits["1000000000000000000000000000"], t50_1);
    info.eval->multiply_plain(ss[13], bits["0001000000000000000000000000"], t50_2);
    info.eval->multiply_plain(ss[22], bits["0000000000000000000000000010"], t50_3);
    info.eval->add_many({t50_1, t50_2, t50_3}, ts[50]);
    
    
    // __t51 = blend(__s32@1000000000000000000000000000, __s40@0001000000000000000000000000, __s39@0000000000000000000000000010)
    ctxt t51_1, t51_2, t51_3;
    info.eval->multiply_plain(ss[32], bits["1000000000000000000000000000"], t51_1);
    info.eval->multiply_plain(ss[40], bits["0001000000000000000000000000"], t51_2);
    info.eval->multiply_plain(ss[39], bits["0000000000000000000000000010"], t51_3);
    info.eval->add_many({t51_1, t51_2, t51_3}, ts[51]);
    
    
    // __t52 = blend(__s3@0000000000000000100000000000, __s7@0000000000000000000000000001)
    ctxt t52_1, t52_2;
    info.eval->multiply_plain(ss[3], bits["0000000000000000100000000000"], t52_1);
    info.eval->multiply_plain(ss[7], bits["0000000000000000000000000001"], t52_2);
    info.eval->add(t52_1, t52_2, ts[52]);
    
    
    // __t53 = blend(__s30@0000000000000000100000000000, __s25@0000000000000000000000000001)
    ctxt t53_1, t53_2;
    info.eval->multiply_plain(ss[30], bits["0000000000000000100000000000"], t53_1);
    info.eval->multiply_plain(ss[25], bits["0000000000000000000000000001"], t53_2);
    info.eval->add(t53_1, t53_2, ts[53]);
    
    
    // __t54 = blend(__v24@0001000000000000000000000000, __v14@0000000000000001000000000000, __v24@0000000000000000100000000001, __v4@0000000000000000000000000100, __v23@0000000000000000000000000010)
    ctxt t54_1, t54_2, t54_3, t54_4, t54_5;
    info.eval->multiply_plain(vs[24], bits["0001000000000000000000000000"], t54_1);
    info.eval->multiply_plain(vs[14], bits["0000000000000001000000000000"], t54_2);
    info.eval->multiply_plain(vs[24], bits["0000000000000000100000000001"], t54_3);
    info.eval->multiply_plain(vs[4], bits["0000000000000000000000000100"], t54_4);
    info.eval->multiply_plain(vs[23], bits["0000000000000000000000000010"], t54_5);
    info.eval->add_many({t54_1, t54_2, t54_3, t54_4, t54_5}, ts[54]);
    
    
    // __t55 = blend(__v23@0001000000000000000000000000, __v9@0000000000000001000000000010, __v8@0000000000000000100000000000, __v6@0000000000000000000000000100, __v24@0000000000000000000000000001)
    ctxt t55_1, t55_2, t55_3, t55_4, t55_5;
    info.eval->multiply_plain(vs[23], bits["0001000000000000000000000000"], t55_1);
    info.eval->multiply_plain(vs[9], bits["0000000000000001000000000010"], t55_2);
    info.eval->multiply_plain(vs[8], bits["0000000000000000100000000000"], t55_3);
    info.eval->multiply_plain(vs[6], bits["0000000000000000000000000100"], t55_4);
    info.eval->multiply_plain(vs[24], bits["0000000000000000000000000001"], t55_5);
    info.eval->add_many({t55_1, t55_2, t55_3, t55_4, t55_5}, ts[55]);
    
    info.eval->multiply(ts[44], ts[45], vs[31]); // __v31 = __t44 * __t45
    info.eval->relinearize_inplace(vs[31], rk);
    info.eval->rotate_rows(vs[31], -4, gk, ss[59]); // __s59 = __v31 >> 4
    info.eval->rotate_rows(vs[31], -5, gk, ss[60]); // __s60 = __v31 >> 5
    
    // __t56 = blend(__v22@0000000000000000000000001000, __v17@0000000000000000000000000010, __v31@0000000000000000000000000001)
    ctxt t56_1, t56_2, t56_3;
    info.eval->multiply_plain(vs[22], bits["0000000000000000000000001000"], t56_1);
    info.eval->multiply_plain(vs[17], bits["0000000000000000000000000010"], t56_2);
    info.eval->multiply_plain(vs[31], bits["0000000000000000000000000001"], t56_3);
    info.eval->add_many({t56_1, t56_2, t56_3}, ts[56]);
    
    
    // __t57 = blend(__v25@0000000000000000000000001000, __v31@0000000000000000000000000010, __v27@0000000000000000000000000001)
    ctxt t57_1, t57_2, t57_3;
    info.eval->multiply_plain(vs[25], bits["0000000000000000000000001000"], t57_1);
    info.eval->multiply_plain(vs[31], bits["0000000000000000000000000010"], t57_2);
    info.eval->multiply_plain(vs[27], bits["0000000000000000000000000001"], t57_3);
    info.eval->add_many({t57_1, t57_2, t57_3}, ts[57]);
    
    info.eval->add(ts[46], ts[47], vs[32]); // __v32 = __t46 + __t47
    
    // __t58 = blend(__v23@1000000000000000000000000000, __v13@0100000000000000000000000000, __v13@0000100000000000000000000000, __v9@0000000001000000000000000000, __v16@0000000000000000000100000000, __v26@0000000000000000000000000100)
    ctxt t58_1, t58_2, t58_3, t58_4, t58_5, t58_6;
    info.eval->multiply_plain(vs[23], bits["1000000000000000000000000000"], t58_1);
    info.eval->multiply_plain(vs[13], bits["0100000000000000000000000000"], t58_2);
    info.eval->multiply_plain(vs[13], bits["0000100000000000000000000000"], t58_3);
    info.eval->multiply_plain(vs[9], bits["0000000001000000000000000000"], t58_4);
    info.eval->multiply_plain(vs[16], bits["0000000000000000000100000000"], t58_5);
    info.eval->multiply_plain(vs[26], bits["0000000000000000000000000100"], t58_6);
    info.eval->add_many({t58_1, t58_2, t58_3, t58_4, t58_5, t58_6}, ts[58]);
    
    
    // __t59 = blend(__v15@1000000000000000000000000000, __v23@0100000000000000000000000000, __v6@0000100000000000000000000000, __v4@0000000001000000000000000000, __v26@0000000000000000000100000000, __v5@0000000000000000000000000100)
    ctxt t59_1, t59_2, t59_3, t59_4, t59_5, t59_6;
    info.eval->multiply_plain(vs[15], bits["1000000000000000000000000000"], t59_1);
    info.eval->multiply_plain(vs[23], bits["0100000000000000000000000000"], t59_2);
    info.eval->multiply_plain(vs[6], bits["0000100000000000000000000000"], t59_3);
    info.eval->multiply_plain(vs[4], bits["0000000001000000000000000000"], t59_4);
    info.eval->multiply_plain(vs[26], bits["0000000000000000000100000000"], t59_5);
    info.eval->multiply_plain(vs[5], bits["0000000000000000000000000100"], t59_6);
    info.eval->add_many({t59_1, t59_2, t59_3, t59_4, t59_5, t59_6}, ts[59]);
    
    
    // __t60 = blend(__s9@0000000000001000000000000000, __s13@0000000000000100000000000000, __s21@0000000000000000000000010000)
    ctxt t60_1, t60_2, t60_3;
    info.eval->multiply_plain(ss[9], bits["0000000000001000000000000000"], t60_1);
    info.eval->multiply_plain(ss[13], bits["0000000000000100000000000000"], t60_2);
    info.eval->multiply_plain(ss[21], bits["0000000000000000000000010000"], t60_3);
    info.eval->add_many({t60_1, t60_2, t60_3}, ts[60]);
    
    
    // __t61 = blend(__s31@0000000000001000000000000000, __s44@0000000000000100000000000000, __s48@0000000000000000000000010000)
    ctxt t61_1, t61_2, t61_3;
    info.eval->multiply_plain(ss[31], bits["0000000000001000000000000000"], t61_1);
    info.eval->multiply_plain(ss[44], bits["0000000000000100000000000000"], t61_2);
    info.eval->multiply_plain(ss[48], bits["0000000000000000000000010000"], t61_3);
    info.eval->add_many({t61_1, t61_2, t61_3}, ts[61]);
    
    info.eval->sub(ts[60], ts[61], vs[34]); // __v34 = __t60 - __t61
    info.eval->add(vs[28], vs[31], vs[35]); // __v35 = __v28 + __v31
    
    // __t62 = blend(__v6@0000000000001000000000000000, __v34@0000000000000100000000010000, __v12@0000000000000000000010000000)
    ctxt t62_1, t62_2, t62_3;
    info.eval->multiply_plain(vs[6], bits["0000000000001000000000000000"], t62_1);
    info.eval->multiply_plain(vs[34], bits["0000000000000100000000010000"], t62_2);
    info.eval->multiply_plain(vs[12], bits["0000000000000000000010000000"], t62_3);
    info.eval->add_many({t62_1, t62_2, t62_3}, ts[62]);
    
    
    // __t63 = blend(__v34@0000000000001000000000000000, __v14@0000000000000100000000000000, __v14@0000000000000000000010000000, __v13@0000000000000000000000010000)
    ctxt t63_1, t63_2, t63_3, t63_4;
    info.eval->multiply_plain(vs[34], bits["0000000000001000000000000000"], t63_1);
    info.eval->multiply_plain(vs[14], bits["0000000000000100000000000000"], t63_2);
    info.eval->multiply_plain(vs[14], bits["0000000000000000000010000000"], t63_3);
    info.eval->multiply_plain(vs[13], bits["0000000000000000000000010000"], t63_4);
    info.eval->add_many({t63_1, t63_2, t63_3, t63_4}, ts[63]);
    
    info.eval->multiply(ts[62], ts[63], vs[36]); // __v36 = __t62 * __t63
    info.eval->relinearize_inplace(vs[36], rk);
    info.eval->rotate_rows(vs[36], -5, gk, ss[63]); // __s63 = __v36 >> 5
    info.eval->rotate_rows(vs[36], -4, gk, ss[64]); // __s64 = __v36 >> 4
    
    // __t64 = blend(__s57@0000010000000000000000000000, __s63@0000000000000000010000000000, __s57@0000000000000000000100000000, __s60@0000000000000000000001000000, __s52@0000000000000000000000010000)
    ctxt t64_1, t64_2, t64_3, t64_4, t64_5;
    info.eval->multiply_plain(ss[57], bits["0000010000000000000000000000"], t64_1);
    info.eval->multiply_plain(ss[63], bits["0000000000000000010000000000"], t64_2);
    info.eval->multiply_plain(ss[57], bits["0000000000000000000100000000"], t64_3);
    info.eval->multiply_plain(ss[60], bits["0000000000000000000001000000"], t64_4);
    info.eval->multiply_plain(ss[52], bits["0000000000000000000000010000"], t64_5);
    info.eval->add_many({t64_1, t64_2, t64_3, t64_4, t64_5}, ts[64]);
    
    
    // __t65 = blend(__s58@0000010000000000000000010000, __s64@0000000000000000010000000000, __s59@0000000000000000000100000000, __s51@0000000000000000000001000000)
    ctxt t65_1, t65_2, t65_3, t65_4;
    info.eval->multiply_plain(ss[58], bits["0000010000000000000000010000"], t65_1);
    info.eval->multiply_plain(ss[64], bits["0000000000000000010000000000"], t65_2);
    info.eval->multiply_plain(ss[59], bits["0000000000000000000100000000"], t65_3);
    info.eval->multiply_plain(ss[51], bits["0000000000000000000001000000"], t65_4);
    info.eval->add_many({t65_1, t65_2, t65_3, t65_4}, ts[65]);
    
    info.eval->add(ts[64], ts[65], vs[37]); // __v37 = __t64 + __t65
    info.eval->add(ss[50], ss[53], vs[38]); // __v38 = __s50 + __s53
    info.eval->add(ss[63], ss[55], vs[39]); // __v39 = __s63 + __s55
    info.eval->add(ss[52], ss[50], vs[40]); // __v40 = __s52 + __s50
    info.eval->add(ss[57], ss[58], vs[41]); // __v41 = __s57 + __s58
    info.eval->add(ss[56], ss[64], vs[42]); // __v42 = __s56 + __s64
    info.eval->add(ss[54], ss[58], vs[43]); // __v43 = __s54 + __s58
    info.eval->add(ss[57], ss[59], vs[44]); // __v44 = __s57 + __s59
    return vs[44];
}
    