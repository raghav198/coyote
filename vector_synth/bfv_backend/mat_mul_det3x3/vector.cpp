
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01000111000", info);
    add_bitstring(bits, "00000000001", info);
    add_bitstring(bits, "00010000001", info);
    add_bitstring(bits, "00000000110", info);
    add_bitstring(bits, "01000010000", info);
    add_bitstring(bits, "00000000010", info);
    add_bitstring(bits, "00000010001", info);
    add_bitstring(bits, "00101000100", info);
    add_bitstring(bits, "00000010100", info);
    add_bitstring(bits, "10000000010", info);
    add_bitstring(bits, "00010000000", info);
    add_bitstring(bits, "00000010010", info);
    add_bitstring(bits, "00100000000", info);
    add_bitstring(bits, "00000100001", info);
    add_bitstring(bits, "10000000001", info);
    add_bitstring(bits, "10000000000", info);
    add_bitstring(bits, "00101000000", info);
    add_bitstring(bits, "01010000000", info);
    add_bitstring(bits, "00000001000", info);
    add_bitstring(bits, "01000000010", info);
    add_bitstring(bits, "10001000000", info);
    add_bitstring(bits, "10000000100", info);
    add_bitstring(bits, "00001000000", info);
    add_bitstring(bits, "00100110000", info);
    add_bitstring(bits, "10000010011", info);
    add_bitstring(bits, "00000000100", info);
    add_bitstring(bits, "00110000000", info);
    add_bitstring(bits, "10000010000", info);
    add_bitstring(bits, "01000100000", info);
    add_bitstring(bits, "01000101000", info);
    add_bitstring(bits, "00000000111", info);
    add_bitstring(bits, "00000011000", info);
    add_bitstring(bits, "00000010000", info);
    add_bitstring(bits, "00100010100", info);
    add_bitstring(bits, "00000100000", info);
    add_bitstring(bits, "01000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(36);
    ts[0] = encrypt_input("11111111110111100110101111111110110111111111011", info);
    ts[2] = encrypt_input("01101111111111111111111010011111111101101111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[29];
    ctxt ss[33];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -8, gk, ss[3]); // __s3 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -9, gk, ss[4]); // __s4 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -1, gk, ss[5]); // __s5 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -5, gk, ss[6]); // __s6 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -7, gk, ss[7]); // __s7 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -4, gk, ss[8]); // __s8 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -10, gk, ss[9]); // __s9 = __v0 >> 10
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[10]); // __s10 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -4, gk, ss[11]); // __s11 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -5, gk, ss[12]); // __s12 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -8, gk, ss[13]); // __s13 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -7, gk, ss[14]); // __s14 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -9, gk, ss[15]); // __s15 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -3, gk, ss[16]); // __s16 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -6, gk, ss[17]); // __s17 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -2, gk, ss[18]); // __s18 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -10, gk, ss[19]); // __s19 = __v1 >> 10
    
    // __t4 = blend(__s0@00100000000, __s1@00010000000, __s7@00001000000, __v0@00000100000, __s3@00000010100, __s4@00000001000, __s2@00000000010)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7;
    info.eval->multiply_plain(ss[0], bits["00100000000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["00010000000"], t4_2);
    info.eval->multiply_plain(ss[7], bits["00001000000"], t4_3);
    info.eval->multiply_plain(vs[0], bits["00000100000"], t4_4);
    info.eval->multiply_plain(ss[3], bits["00000010100"], t4_5);
    info.eval->multiply_plain(ss[4], bits["00000001000"], t4_6);
    info.eval->multiply_plain(ss[2], bits["00000000010"], t4_7);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7}, ts[4]);
    
    
    // __t5 = blend(__s15@00100000000, __s10@00010000000, __s14@00001000000, __s11@00000100000, __s19@00000010000, __s13@00000001000, __v1@00000000110)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7;
    info.eval->multiply_plain(ss[15], bits["00100000000"], t5_1);
    info.eval->multiply_plain(ss[10], bits["00010000000"], t5_2);
    info.eval->multiply_plain(ss[14], bits["00001000000"], t5_3);
    info.eval->multiply_plain(ss[11], bits["00000100000"], t5_4);
    info.eval->multiply_plain(ss[19], bits["00000010000"], t5_5);
    info.eval->multiply_plain(ss[13], bits["00000001000"], t5_6);
    info.eval->multiply_plain(vs[1], bits["00000000110"], t5_7);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s0@10000000001, __s1@01000000000, __s2@00100110000, __s7@00010000000, __s9@00001000000, __v0@00000000010)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(ss[0], bits["10000000001"], t6_1);
    info.eval->multiply_plain(ss[1], bits["01000000000"], t6_2);
    info.eval->multiply_plain(ss[2], bits["00100110000"], t6_3);
    info.eval->multiply_plain(ss[7], bits["00010000000"], t6_4);
    info.eval->multiply_plain(ss[9], bits["00001000000"], t6_5);
    info.eval->multiply_plain(vs[0], bits["00000000010"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6}, ts[6]);
    
    
    // __t7 = blend(__s13@10000000001, __s12@01010000000, __s10@00100000000, __s19@00001000000, __s15@00000100000, __s11@00000010000, __s17@00000000010)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7;
    info.eval->multiply_plain(ss[13], bits["10000000001"], t7_1);
    info.eval->multiply_plain(ss[12], bits["01010000000"], t7_2);
    info.eval->multiply_plain(ss[10], bits["00100000000"], t7_3);
    info.eval->multiply_plain(ss[19], bits["00001000000"], t7_4);
    info.eval->multiply_plain(ss[15], bits["00000100000"], t7_5);
    info.eval->multiply_plain(ss[11], bits["00000010000"], t7_6);
    info.eval->multiply_plain(ss[17], bits["00000000010"], t7_7);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s6@10001000000, __s4@01000000000, __s9@00000010000, __s7@00000000100, __s3@00000000010, __v0@00000000001)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6;
    info.eval->multiply_plain(ss[6], bits["10001000000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["01000000000"], t8_2);
    info.eval->multiply_plain(ss[9], bits["00000010000"], t8_3);
    info.eval->multiply_plain(ss[7], bits["00000000100"], t8_4);
    info.eval->multiply_plain(ss[3], bits["00000000010"], t8_5);
    info.eval->multiply_plain(vs[0], bits["00000000001"], t8_6);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6}, ts[8]);
    
    
    // __t9 = blend(__s15@10000000100, __v1@01000000000, __s12@00001000000, __s13@00000010000, __s18@00000000010, __s14@00000000001)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6;
    info.eval->multiply_plain(ss[15], bits["10000000100"], t9_1);
    info.eval->multiply_plain(vs[1], bits["01000000000"], t9_2);
    info.eval->multiply_plain(ss[12], bits["00001000000"], t9_3);
    info.eval->multiply_plain(ss[13], bits["00000010000"], t9_4);
    info.eval->multiply_plain(ss[18], bits["00000000010"], t9_5);
    info.eval->multiply_plain(ss[14], bits["00000000001"], t9_6);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__s3@10000000000, __s5@00100000000, __s0@00010000000, __s1@00000010000, __s4@00000000010)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(ss[3], bits["10000000000"], t10_1);
    info.eval->multiply_plain(ss[5], bits["00100000000"], t10_2);
    info.eval->multiply_plain(ss[0], bits["00010000000"], t10_3);
    info.eval->multiply_plain(ss[1], bits["00000010000"], t10_4);
    info.eval->multiply_plain(ss[4], bits["00000000010"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__s18@10000000000, __s17@00100000000, __v1@00010000000, __s12@00000010010)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[18], bits["10000000000"], t11_1);
    info.eval->multiply_plain(ss[17], bits["00100000000"], t11_2);
    info.eval->multiply_plain(vs[1], bits["00010000000"], t11_3);
    info.eval->multiply_plain(ss[12], bits["00000010010"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->multiply(ts[00], ts[01], vs[5]); // __v5 = __t00 * __t01
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t12 = blend(__v0@00000010000, __s8@00000001000, __s5@00000000100, __s1@00000000010)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(vs[0], bits["00000010000"], t12_1);
    info.eval->multiply_plain(ss[8], bits["00000001000"], t12_2);
    info.eval->multiply_plain(ss[5], bits["00000000100"], t12_3);
    info.eval->multiply_plain(ss[1], bits["00000000010"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__s18@00000011000, __s16@00000000100, __s14@00000000010)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[18], bits["00000011000"], t13_1);
    info.eval->multiply_plain(ss[16], bits["00000000100"], t13_2);
    info.eval->multiply_plain(ss[14], bits["00000000010"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->multiply(ts[02], ts[03], vs[6]); // __v6 = __t02 * __t03
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__v5@10000010000, __v3@00101000000, __v6@00000000100, __v2@00000000010)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(vs[5], bits["10000010000"], t14_1);
    info.eval->multiply_plain(vs[3], bits["00101000000"], t14_2);
    info.eval->multiply_plain(vs[6], bits["00000000100"], t14_3);
    info.eval->multiply_plain(vs[2], bits["00000000010"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    
    // __t15 = blend(__v4@10000000000, __v2@00101000100, __v6@00000010010)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(vs[4], bits["10000000000"], t15_1);
    info.eval->multiply_plain(vs[2], bits["00101000100"], t15_2);
    info.eval->multiply_plain(vs[6], bits["00000010010"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->add(ts[04], ts[05], vs[7]); // __v7 = __t04 + __t05
    
    // __t16 = blend(__s2@01000000000, __s3@00000100000, __s6@00000010001, __s5@00000001000, __s0@00000000010)
    ctxt t16_1, t16_2, t16_3, t16_4, t16_5;
    info.eval->multiply_plain(ss[2], bits["01000000000"], t16_1);
    info.eval->multiply_plain(ss[3], bits["00000100000"], t16_2);
    info.eval->multiply_plain(ss[6], bits["00000010001"], t16_3);
    info.eval->multiply_plain(ss[5], bits["00000001000"], t16_4);
    info.eval->multiply_plain(ss[0], bits["00000000010"], t16_5);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, t16_5}, ts[16]);
    
    
    // __t17 = blend(__s13@01000000010, __s10@00000100001, __s16@00000010000, __s19@00000001000)
    ctxt t17_1, t17_2, t17_3, t17_4;
    info.eval->multiply_plain(ss[13], bits["01000000010"], t17_1);
    info.eval->multiply_plain(ss[10], bits["00000100001"], t17_2);
    info.eval->multiply_plain(ss[16], bits["00000010000"], t17_3);
    info.eval->multiply_plain(ss[19], bits["00000001000"], t17_4);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4}, ts[17]);
    
    info.eval->multiply(ts[06], ts[07], vs[8]); // __v8 = __t06 * __t07
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t18 = blend(__v7@10000000010, __v4@01000010000, __v3@00010000000, __v2@00000100000, __v6@00000001000, __v8@00000000001)
    ctxt t18_1, t18_2, t18_3, t18_4, t18_5, t18_6;
    info.eval->multiply_plain(vs[7], bits["10000000010"], t18_1);
    info.eval->multiply_plain(vs[4], bits["01000010000"], t18_2);
    info.eval->multiply_plain(vs[3], bits["00010000000"], t18_3);
    info.eval->multiply_plain(vs[2], bits["00000100000"], t18_4);
    info.eval->multiply_plain(vs[6], bits["00000001000"], t18_5);
    info.eval->multiply_plain(vs[8], bits["00000000001"], t18_6);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4, t18_5, t18_6}, ts[18]);
    
    
    // __t19 = blend(__v3@10000010011, __v8@01000101000, __v2@00010000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[3], bits["10000010011"], t19_1);
    info.eval->multiply_plain(vs[8], bits["01000101000"], t19_2);
    info.eval->multiply_plain(vs[2], bits["00010000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->add(ts[08], ts[09], vs[9]); // __v9 = __t08 + __t09
    info.eval->rotate_rows(vs[9], -4, gk, ss[20]); // __s20 = __v9 >> 4
    
    // __t20 = blend(__v9@01000111000, __v7@00001000000, __v8@00000000010)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(vs[9], bits["01000111000"], t20_1);
    info.eval->multiply_plain(vs[7], bits["00001000000"], t20_2);
    info.eval->multiply_plain(vs[8], bits["00000000010"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3}, ts[20]);
    
    
    // __t21 = blend(__v3@01000100000, __v4@00001000000, __v8@00000010000, __v2@00000001000, __v5@00000000010)
    ctxt t21_1, t21_2, t21_3, t21_4, t21_5;
    info.eval->multiply_plain(vs[3], bits["01000100000"], t21_1);
    info.eval->multiply_plain(vs[4], bits["00001000000"], t21_2);
    info.eval->multiply_plain(vs[8], bits["00000010000"], t21_3);
    info.eval->multiply_plain(vs[2], bits["00000001000"], t21_4);
    info.eval->multiply_plain(vs[5], bits["00000000010"], t21_5);
    info.eval->add_many({t21_1, t21_2, t21_3, t21_4, t21_5}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[10]); // __v10 = __t20 + __t21
    info.eval->rotate_rows(vs[10], -8, gk, ss[21]); // __s21 = __v10 >> 8
    info.eval->rotate_rows(vs[10], -3, gk, ss[22]); // __s22 = __v10 >> 3
    info.eval->rotate_rows(vs[10], -10, gk, ss[23]); // __s23 = __v10 >> 10
    info.eval->rotate_rows(vs[10], -2, gk, ss[24]); // __s24 = __v10 >> 2
    
    // __t22 = blend(__v7@00100010100, __v9@00010000001, __v10@00000000010)
    ctxt t22_1, t22_2, t22_3;
    info.eval->multiply_plain(vs[7], bits["00100010100"], t22_1);
    info.eval->multiply_plain(vs[9], bits["00010000001"], t22_2);
    info.eval->multiply_plain(vs[10], bits["00000000010"], t22_3);
    info.eval->add_many({t22_1, t22_2, t22_3}, ts[22]);
    
    
    // __t23 = blend(__v5@00110000000, __v2@00000010000, __v4@00000000111)
    ctxt t23_1, t23_2, t23_3;
    info.eval->multiply_plain(vs[5], bits["00110000000"], t23_1);
    info.eval->multiply_plain(vs[2], bits["00000010000"], t23_2);
    info.eval->multiply_plain(vs[4], bits["00000000111"], t23_3);
    info.eval->add_many({t23_1, t23_2, t23_3}, ts[23]);
    
    info.eval->add(ts[22], ts[23], vs[11]); // __v11 = __t22 + __t23
    info.eval->rotate_rows(vs[11], -7, gk, ss[25]); // __s25 = __v11 >> 7
    info.eval->rotate_rows(vs[11], -1, gk, ss[26]); // __s26 = __v11 >> 1
    info.eval->rotate_rows(vs[11], -10, gk, ss[27]); // __s27 = __v11 >> 10
    
    // __t24 = blend(__v10@00000010000, __v9@00000000010)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[10], bits["00000010000"], t24_1);
    info.eval->multiply_plain(vs[9], bits["00000000010"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    info.eval->multiply(vs[11], ts[24], vs[12]); // __v12 = __v11 * __t24
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -1, gk, ss[28]); // __s28 = __v12 >> 1
    info.eval->rotate_rows(vs[12], -9, gk, ss[29]); // __s29 = __v12 >> 9
    info.eval->multiply(vs[0], ss[19], vs[13]); // __v13 = __v0 * __s19
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->multiply(vs[0], ss[12], vs[14]); // __v14 = __v0 * __s12
    info.eval->relinearize_inplace(vs[14], rk);
    
    // __t25 = blend(__v0@00001000000, __s24@00000000010)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(vs[0], bits["00001000000"], t25_1);
    info.eval->multiply_plain(ss[24], bits["00000000010"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    
    // __t26 = blend(__s14@00001000000, __s25@00000000010)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(ss[14], bits["00001000000"], t26_1);
    info.eval->multiply_plain(ss[25], bits["00000000010"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    info.eval->multiply(ts[25], ts[26], vs[15]); // __v15 = __t25 * __t26
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->add(vs[13], vs[15], vs[17]); // __v17 = __v13 + __v15
    info.eval->add(vs[17], vs[14], vs[18]); // __v18 = __v17 + __v14
    info.eval->multiply(vs[18], ss[26], vs[19]); // __v19 = __v18 * __s26
    info.eval->relinearize_inplace(vs[19], rk);
    
    // __t27 = blend(__v0@00001000000, __s26@00000000010)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(vs[0], bits["00001000000"], t27_1);
    info.eval->multiply_plain(ss[26], bits["00000000010"], t27_2);
    info.eval->add(t27_1, t27_2, ts[27]);
    
    
    // __t28 = blend(__s12@00001000000, __s21@00000000010)
    ctxt t28_1, t28_2;
    info.eval->multiply_plain(ss[12], bits["00001000000"], t28_1);
    info.eval->multiply_plain(ss[21], bits["00000000010"], t28_2);
    info.eval->add(t28_1, t28_2, ts[28]);
    
    info.eval->multiply(ts[27], ts[28], vs[20]); // __v20 = __t27 * __t28
    info.eval->relinearize_inplace(vs[20], rk);
    info.eval->multiply(vs[0], ss[14], vs[21]); // __v21 = __v0 * __s14
    info.eval->relinearize_inplace(vs[21], rk);
    
    // __t29 = blend(__v13@00001000000, __v20@00000000010)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(vs[13], bits["00001000000"], t29_1);
    info.eval->multiply_plain(vs[20], bits["00000000010"], t29_2);
    info.eval->add(t29_1, t29_2, ts[29]);
    
    
    // __t30 = blend(__v21@00001000000, __v15@00000000010)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(vs[21], bits["00001000000"], t30_1);
    info.eval->multiply_plain(vs[15], bits["00000000010"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    info.eval->add(ts[29], ts[20], vs[22]); // __v22 = __t29 + __t20
    info.eval->add(vs[22], vs[20], vs[23]); // __v23 = __v22 + __v20
    
    // __t31 = blend(__v23@00001000000, __s27@00000000010)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(vs[23], bits["00001000000"], t31_1);
    info.eval->multiply_plain(ss[27], bits["00000000010"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    
    // __t32 = blend(__s20@00001000000, __v22@00000000010)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(ss[20], bits["00001000000"], t32_1);
    info.eval->multiply_plain(vs[22], bits["00000000010"], t32_2);
    info.eval->add(t32_1, t32_2, ts[32]);
    
    info.eval->multiply(ts[21], ts[22], vs[24]); // __v24 = __t21 * __t22
    info.eval->relinearize_inplace(vs[24], rk);
    info.eval->rotate_rows(vs[24], -5, gk, ss[30]); // __s30 = __v24 >> 5
    
    // __t33 = blend(__v24@00001000000, __s29@00000001000)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(vs[24], bits["00001000000"], t33_1);
    info.eval->multiply_plain(ss[29], bits["00000001000"], t33_2);
    info.eval->add(t33_1, t33_2, ts[33]);
    
    
    // __t34 = blend(__v19@00001000000, __s28@00000001000)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[19], bits["00001000000"], t34_1);
    info.eval->multiply_plain(ss[28], bits["00000001000"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    info.eval->add(ts[23], ts[24], vs[25]); // __v25 = __t23 + __t24
    
    // __t35 = blend(__s23@00001000000, __s22@00000001000)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(ss[23], bits["00001000000"], t35_1);
    info.eval->multiply_plain(ss[22], bits["00000001000"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->multiply(ts[25], vs[25], vs[26]); // __v26 = __t25 * __v25
    info.eval->relinearize_inplace(vs[26], rk);
    info.eval->rotate_rows(vs[26], -10, gk, ss[31]); // __s31 = __v26 >> 10
    info.eval->rotate_rows(vs[26], -7, gk, ss[32]); // __s32 = __v26 >> 7
    info.eval->sub(ss[32], ss[31], vs[27]); // __v27 = __s32 - __s31
    info.eval->add(vs[27], ss[30], vs[28]); // __v28 = __v27 + __s30
    return vs[28];
}
    