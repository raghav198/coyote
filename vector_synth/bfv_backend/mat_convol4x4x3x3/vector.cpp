
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0010110000000000", info);
    add_bitstring(bits, "0010100000000000", info);
    add_bitstring(bits, "0010000000000000", info);
    add_bitstring(bits, "1000100000000000", info);
    add_bitstring(bits, "0000010000000000", info);
    add_bitstring(bits, "0000110000000000", info);
    add_bitstring(bits, "0000100000000000", info);
    add_bitstring(bits, "1010000000000000", info);
    add_bitstring(bits, "0010010000000000", info);
    add_bitstring(bits, "1000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(31);
    ts[0] = encrypt_input("11110111111101111111110101111011110111111111111111110111101111111111111111111111", info);
    ts[2] = encrypt_input("1111111111111111111000110100001101111111110111111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[19];
    ctxt ss[29];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -4, gk, ss[1]); // __s1 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -15, gk, ss[2]); // __s2 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -14, gk, ss[3]); // __s3 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -1, gk, ss[4]); // __s4 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -13, gk, ss[5]); // __s5 = __v0 >> 13
    info.eval->rotate_rows(vs[0], -8, gk, ss[6]); // __s6 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -9, gk, ss[7]); // __s7 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -11, gk, ss[8]); // __s8 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -12, gk, ss[9]); // __s9 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -7, gk, ss[10]); // __s10 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -6, gk, ss[11]); // __s11 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -5, gk, ss[12]); // __s12 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -3, gk, ss[13]); // __s13 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -2, gk, ss[14]); // __s14 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -4, gk, ss[15]); // __s15 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -5, gk, ss[16]); // __s16 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -1, gk, ss[17]); // __s17 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -3, gk, ss[18]); // __s18 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -15, gk, ss[19]); // __s19 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -14, gk, ss[20]); // __s20 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -13, gk, ss[21]); // __s21 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -10, gk, ss[22]); // __s22 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -12, gk, ss[23]); // __s23 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -8, gk, ss[24]); // __s24 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -11, gk, ss[25]); // __s25 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -6, gk, ss[26]); // __s26 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -9, gk, ss[27]); // __s27 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -7, gk, ss[28]); // __s28 = __v1 >> 7
    
    // __t4 = blend(__s15@1000100000000000, __s14@0010000000000000, __s24@0000010000000000)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[15], bits["1000100000000000"], t4_1);
    info.eval->multiply_plain(ss[14], bits["0010000000000000"], t4_2);
    info.eval->multiply_plain(ss[24], bits["0000010000000000"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__s3@1000000000000000, __s12@0010000000000000, __s8@0000100000000000, __s10@0000010000000000)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(ss[3], bits["1000000000000000"], t5_1);
    info.eval->multiply_plain(ss[12], bits["0010000000000000"], t5_2);
    info.eval->multiply_plain(ss[8], bits["0000100000000000"], t5_3);
    info.eval->multiply_plain(ss[10], bits["0000010000000000"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s18@1000100000000000, __v1@0010000000000000, __s22@0000010000000000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[18], bits["1000100000000000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["0010000000000000"], t6_2);
    info.eval->multiply_plain(ss[22], bits["0000010000000000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s10@1000000000000000, __s7@0010000000000000, __s4@0000100000000000, __s3@0000010000000000)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[10], bits["1000000000000000"], t7_1);
    info.eval->multiply_plain(ss[7], bits["0010000000000000"], t7_2);
    info.eval->multiply_plain(ss[4], bits["0000100000000000"], t7_3);
    info.eval->multiply_plain(ss[3], bits["0000010000000000"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s16@1000000000000000, __s17@0010000000000000, __s22@0000100000000000, __s15@0000010000000000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[16], bits["1000000000000000"], t8_1);
    info.eval->multiply_plain(ss[17], bits["0010000000000000"], t8_2);
    info.eval->multiply_plain(ss[22], bits["0000100000000000"], t8_3);
    info.eval->multiply_plain(ss[15], bits["0000010000000000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s2@1000000000000000, __s11@0010000000000000, __s10@0000100000000000, __s1@0000010000000000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[2], bits["1000000000000000"], t9_1);
    info.eval->multiply_plain(ss[11], bits["0010000000000000"], t9_2);
    info.eval->multiply_plain(ss[10], bits["0000100000000000"], t9_3);
    info.eval->multiply_plain(ss[1], bits["0000010000000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__s26@1000000000000000, __s23@0010000000000000, __s17@0000100000000000, __s19@0000010000000000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[26], bits["1000000000000000"], t10_1);
    info.eval->multiply_plain(ss[23], bits["0010000000000000"], t10_2);
    info.eval->multiply_plain(ss[17], bits["0000100000000000"], t10_3);
    info.eval->multiply_plain(ss[19], bits["0000010000000000"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s11@1000000000000000, __s3@0010000000000000, __s1@0000100000000000, __s6@0000010000000000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[11], bits["1000000000000000"], t11_1);
    info.eval->multiply_plain(ss[3], bits["0010000000000000"], t11_2);
    info.eval->multiply_plain(ss[1], bits["0000100000000000"], t11_3);
    info.eval->multiply_plain(ss[6], bits["0000010000000000"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->multiply(ts[00], ts[01], vs[5]); // __v5 = __t00 * __t01
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t12 = blend(__s22@1000000000000000, __s24@0010000000000000, __s20@0000100000000000, __s25@0000010000000000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[22], bits["1000000000000000"], t12_1);
    info.eval->multiply_plain(ss[24], bits["0010000000000000"], t12_2);
    info.eval->multiply_plain(ss[20], bits["0000100000000000"], t12_3);
    info.eval->multiply_plain(ss[25], bits["0000010000000000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__s12@1000000000000000, __s10@0010000000000000, __s2@0000100000000000, __s7@0000010000000000)
    ctxt t13_1, t13_2, t13_3, t13_4;
    info.eval->multiply_plain(ss[12], bits["1000000000000000"], t13_1);
    info.eval->multiply_plain(ss[10], bits["0010000000000000"], t13_2);
    info.eval->multiply_plain(ss[2], bits["0000100000000000"], t13_3);
    info.eval->multiply_plain(ss[7], bits["0000010000000000"], t13_4);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4}, ts[13]);
    
    info.eval->multiply(ts[02], ts[03], vs[6]); // __v6 = __t02 * __t03
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__v6@1000100000000000, __v5@0010010000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[6], bits["1000100000000000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["0010010000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v5@1000000000000000, __v6@0010010000000000, __v4@0000100000000000)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(vs[5], bits["1000000000000000"], t15_1);
    info.eval->multiply_plain(vs[6], bits["0010010000000000"], t15_2);
    info.eval->multiply_plain(vs[4], bits["0000100000000000"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->add(ts[04], ts[05], vs[7]); // __v7 = __t04 + __t05
    
    // __t16 = blend(__s21@1000000000000000, __s26@0010000000000000, __s24@0000100000000000, __s27@0000010000000000)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(ss[21], bits["1000000000000000"], t16_1);
    info.eval->multiply_plain(ss[26], bits["0010000000000000"], t16_2);
    info.eval->multiply_plain(ss[24], bits["0000100000000000"], t16_3);
    info.eval->multiply_plain(ss[27], bits["0000010000000000"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4}, ts[16]);
    
    
    // __t17 = blend(__s13@1000000000000000, __s6@0010100000000000, __s5@0000010000000000)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(ss[13], bits["1000000000000000"], t17_1);
    info.eval->multiply_plain(ss[6], bits["0010100000000000"], t17_2);
    info.eval->multiply_plain(ss[5], bits["0000010000000000"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3}, ts[17]);
    
    info.eval->multiply(ts[06], ts[07], vs[8]); // __v8 = __t06 * __t07
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t18 = blend(__v2@1000000000000000, __v8@0010110000000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[2], bits["1000000000000000"], t18_1);
    info.eval->multiply_plain(vs[8], bits["0010110000000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->add(vs[7], ts[08], vs[9]); // __v9 = __v7 + __t08
    
    // __t19 = blend(__s20@1000000000000000, __s19@0010000000000000, __s14@0000110000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(ss[20], bits["1000000000000000"], t19_1);
    info.eval->multiply_plain(ss[19], bits["0010000000000000"], t19_2);
    info.eval->multiply_plain(ss[14], bits["0000110000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    
    // __t20 = blend(__s5@1010000000000000, __s11@0000100000000000, __s9@0000010000000000)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(ss[5], bits["1010000000000000"], t20_1);
    info.eval->multiply_plain(ss[11], bits["0000100000000000"], t20_2);
    info.eval->multiply_plain(ss[9], bits["0000010000000000"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3}, ts[20]);
    
    info.eval->multiply(ts[09], ts[20], vs[10]); // __v10 = __t09 * __t20
    info.eval->relinearize_inplace(vs[10], rk);
    
    // __t21 = blend(__s19@1000000000000000, __s16@0010010000000000, __s27@0000100000000000)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(ss[19], bits["1000000000000000"], t21_1);
    info.eval->multiply_plain(ss[16], bits["0010010000000000"], t21_2);
    info.eval->multiply_plain(ss[27], bits["0000100000000000"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3}, ts[21]);
    
    
    // __t22 = blend(__s6@1000000000000000, __s0@0010010000000000, __s12@0000100000000000)
    ctxt t22_1, t22_2, t22_3;
    info.eval->multiply_plain(ss[6], bits["1000000000000000"], t22_1);
    info.eval->multiply_plain(ss[0], bits["0010010000000000"], t22_2);
    info.eval->multiply_plain(ss[12], bits["0000100000000000"], t22_3);
    info.eval->add_many({t22_1, t22_2, t22_3}, ts[22]);
    
    info.eval->multiply(ts[21], ts[22], vs[11]); // __v11 = __t21 * __t22
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t23 = blend(__v1@1000000000000000, __s28@0010100000000000, __s18@0000010000000000)
    ctxt t23_1, t23_2, t23_3;
    info.eval->multiply_plain(vs[1], bits["1000000000000000"], t23_1);
    info.eval->multiply_plain(ss[28], bits["0010100000000000"], t23_2);
    info.eval->multiply_plain(ss[18], bits["0000010000000000"], t23_3);
    info.eval->add_many({t23_1, t23_2, t23_3}, ts[23]);
    
    
    // __t24 = blend(__s1@1000000000000000, __s2@0010000000000000, __s3@0000100000000000, __s11@0000010000000000)
    ctxt t24_1, t24_2, t24_3, t24_4;
    info.eval->multiply_plain(ss[1], bits["1000000000000000"], t24_1);
    info.eval->multiply_plain(ss[2], bits["0010000000000000"], t24_2);
    info.eval->multiply_plain(ss[3], bits["0000100000000000"], t24_3);
    info.eval->multiply_plain(ss[11], bits["0000010000000000"], t24_4);
    info.eval->add_many({t24_1, t24_2, t24_3, t24_4}, ts[24]);
    
    info.eval->multiply(ts[23], ts[24], vs[12]); // __v12 = __t23 * __t24
    info.eval->relinearize_inplace(vs[12], rk);
    
    // __t25 = blend(__v8@1000000000000000, __v10@0010010000000000, __v5@0000100000000000)
    ctxt t25_1, t25_2, t25_3;
    info.eval->multiply_plain(vs[8], bits["1000000000000000"], t25_1);
    info.eval->multiply_plain(vs[10], bits["0010010000000000"], t25_2);
    info.eval->multiply_plain(vs[5], bits["0000100000000000"], t25_3);
    info.eval->add_many({t25_1, t25_2, t25_3}, ts[25]);
    
    info.eval->add(vs[9], ts[25], vs[13]); // __v13 = __v9 + __t25
    
    // __t26 = blend(__v12@1000000000000000, __v2@0010100000000000, __v11@0000010000000000)
    ctxt t26_1, t26_2, t26_3;
    info.eval->multiply_plain(vs[12], bits["1000000000000000"], t26_1);
    info.eval->multiply_plain(vs[2], bits["0010100000000000"], t26_2);
    info.eval->multiply_plain(vs[11], bits["0000010000000000"], t26_3);
    info.eval->add_many({t26_1, t26_2, t26_3}, ts[26]);
    
    info.eval->add(vs[13], ts[26], vs[14]); // __v14 = __v13 + __t26
    
    // __t27 = blend(__v11@1000000000000000, __v4@0010010000000000, __v3@0000100000000000)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(vs[11], bits["1000000000000000"], t27_1);
    info.eval->multiply_plain(vs[4], bits["0010010000000000"], t27_2);
    info.eval->multiply_plain(vs[3], bits["0000100000000000"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3}, ts[27]);
    
    info.eval->add(vs[14], ts[27], vs[15]); // __v15 = __v14 + __t27
    
    // __t28 = blend(__v3@1000000000000000, __v11@0010000000000000, __v12@0000100000000000, __v2@0000010000000000)
    ctxt t28_1, t28_2, t28_3, t28_4;
    info.eval->multiply_plain(vs[3], bits["1000000000000000"], t28_1);
    info.eval->multiply_plain(vs[11], bits["0010000000000000"], t28_2);
    info.eval->multiply_plain(vs[12], bits["0000100000000000"], t28_3);
    info.eval->multiply_plain(vs[2], bits["0000010000000000"], t28_4);
    info.eval->add_many({t28_1, t28_2, t28_3, t28_4}, ts[28]);
    
    info.eval->add(vs[15], ts[28], vs[16]); // __v16 = __v15 + __t28
    
    // __t29 = blend(__v10@1000100000000000, __v3@0010000000000000, __v12@0000010000000000)
    ctxt t29_1, t29_2, t29_3;
    info.eval->multiply_plain(vs[10], bits["1000100000000000"], t29_1);
    info.eval->multiply_plain(vs[3], bits["0010000000000000"], t29_2);
    info.eval->multiply_plain(vs[12], bits["0000010000000000"], t29_3);
    info.eval->add_many({t29_1, t29_2, t29_3}, ts[29]);
    
    info.eval->add(vs[16], ts[29], vs[17]); // __v17 = __v16 + __t29
    
    // __t30 = blend(__v4@1000000000000000, __v12@0010000000000000, __v11@0000100000000000, __v3@0000010000000000)
    ctxt t30_1, t30_2, t30_3, t30_4;
    info.eval->multiply_plain(vs[4], bits["1000000000000000"], t30_1);
    info.eval->multiply_plain(vs[12], bits["0010000000000000"], t30_2);
    info.eval->multiply_plain(vs[11], bits["0000100000000000"], t30_3);
    info.eval->multiply_plain(vs[3], bits["0000010000000000"], t30_4);
    info.eval->add_many({t30_1, t30_2, t30_3, t30_4}, ts[30]);
    
    info.eval->add(vs[17], ts[20], vs[18]); // __v18 = __v17 + __t20
    return vs[18];
}
    