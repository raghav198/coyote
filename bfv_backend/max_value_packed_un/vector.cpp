
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000100101000000000", info);
    add_bitstring(bits, "000000000001000001", info);
    add_bitstring(bits, "000000000001000010", info);
    add_bitstring(bits, "000000000100000001", info);
    add_bitstring(bits, "000000100000010100", info);
    add_bitstring(bits, "000010000000000000", info);
    add_bitstring(bits, "000100011100100000", info);
    add_bitstring(bits, "000000000001000011", info);
    add_bitstring(bits, "000001000000000000", info);
    add_bitstring(bits, "000100000000000000", info);
    add_bitstring(bits, "000000000101000000", info);
    add_bitstring(bits, "000000100000000000", info);
    add_bitstring(bits, "000000001011000000", info);
    add_bitstring(bits, "010000000000000000", info);
    add_bitstring(bits, "010000000000001000", info);
    add_bitstring(bits, "000000000100000000", info);
    add_bitstring(bits, "010000000000000010", info);
    add_bitstring(bits, "100010000000000000", info);
    add_bitstring(bits, "000000000000100000", info);
    add_bitstring(bits, "000000001000000000", info);
    add_bitstring(bits, "000000000001000000", info);
    add_bitstring(bits, "000000000100000100", info);
    add_bitstring(bits, "010010000000000000", info);
    add_bitstring(bits, "000000000000100100", info);
    add_bitstring(bits, "000000000000000010", info);
    add_bitstring(bits, "000000101000000000", info);
    add_bitstring(bits, "000000000010000000", info);
    add_bitstring(bits, "000000000000001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(23);
    ts[0] = encrypt_input("011111111111111111111111111111111111111111111111111000111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111011111111111111111111111100", info);
    ts[1] = encrypt_input("011111111111111111111111111111111111111111111111111000111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111011111111111111111111111100", info);
    ts[2] = encrypt_input("011111111111111111111111100001111111111111111111111111000011111111111111111111111110011111111111111111111111110011111111111111111111111110", info);
    ts[3] = encrypt_input("011111111111111111111111100001111111111111111111111111000011111111111111111111111110011111111111111111111111110011111111111111111111111110", info);
    ts[4] = encrypt_input("110110111101111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[19];
    ctxt ss[30];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -17, gk, ss[1]); // __s1 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -3, gk, ss[2]); // __s2 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -8, gk, ss[3]); // __s3 = __v0 >> 8
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -4, gk, ss[4]); // __s4 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -6, gk, ss[5]); // __s5 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -1, gk, ss[6]); // __s6 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -2, gk, ss[7]); // __s7 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -9, gk, ss[8]); // __s8 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -16, gk, ss[9]); // __s9 = __v1 >> 16
    
    // __t5 = blend(__s3@100010000000000000, __v0@010000000000001000, __s0@000100011100100000, __s1@000000100000010100, __s2@000000000001000011)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[3], bits["100010000000000000"], t5_1);
    info.eval->multiply_plain(vs[0], bits["010000000000001000"], t5_2);
    info.eval->multiply_plain(ss[0], bits["000100011100100000"], t5_3);
    info.eval->multiply_plain(ss[1], bits["000000100000010100"], t5_4);
    info.eval->multiply_plain(ss[2], bits["000000000001000011"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5}, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->rotate_rows(vs[2], -6, gk, ss[10]); // __s10 = __v2 >> 6
    info.eval->rotate_rows(vs[2], -2, gk, ss[11]); // __s11 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -16, gk, ss[12]); // __s12 = __v2 >> 16
    info.eval->rotate_rows(vs[2], -17, gk, ss[13]); // __s13 = __v2 >> 17
    info.eval->rotate_rows(vs[2], -1, gk, ss[14]); // __s14 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -9, gk, ss[15]); // __s15 = __v2 >> 9
    
    // __t6 = blend(__v2@010000000000000010, __s3@000010000000000000, __s15@000000001000000000, __s0@000000000100000100, __s10@000000000010000000, __s2@000000000001000001, __s12@000000000000100000, __v0@000000000000001000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7, t6_8;
    info.eval->multiply_plain(vs[2], bits["010000000000000010"], t6_1);
    info.eval->multiply_plain(ss[3], bits["000010000000000000"], t6_2);
    info.eval->multiply_plain(ss[15], bits["000000001000000000"], t6_3);
    info.eval->multiply_plain(ss[0], bits["000000000100000100"], t6_4);
    info.eval->multiply_plain(ss[10], bits["000000000010000000"], t6_5);
    info.eval->multiply_plain(ss[2], bits["000000000001000001"], t6_6);
    info.eval->multiply_plain(ss[12], bits["000000000000100000"], t6_7);
    info.eval->multiply_plain(vs[0], bits["000000000000001000"], t6_8);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7, t6_8}, ts[6]);
    
    
    // __t7 = blend(__s8@010010000000000000, __s9@000000001000000000, __s4@000000000100000001, __v1@000000000010000000, __s5@000000000001000010, __s7@000000000000100100, __s6@000000000000001000)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7;
    info.eval->multiply_plain(ss[8], bits["010010000000000000"], t7_1);
    info.eval->multiply_plain(ss[9], bits["000000001000000000"], t7_2);
    info.eval->multiply_plain(ss[4], bits["000000000100000001"], t7_3);
    info.eval->multiply_plain(vs[1], bits["000000000010000000"], t7_4);
    info.eval->multiply_plain(ss[5], bits["000000000001000010"], t7_5);
    info.eval->multiply_plain(ss[7], bits["000000000000100100"], t7_6);
    info.eval->multiply_plain(ss[6], bits["000000000000001000"], t7_7);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -4, gk, ss[16]); // __s16 = __v3 >> 4
    info.eval->rotate_rows(vs[3], -16, gk, ss[17]); // __s17 = __v3 >> 16
    info.eval->rotate_rows(vs[3], -9, gk, ss[18]); // __s18 = __v3 >> 9
    info.eval->rotate_rows(vs[3], -13, gk, ss[19]); // __s19 = __v3 >> 13
    
    // __t8 = blend(__v0@010000000000000000, __s11@000000000001000000, __s14@000000000000001000, __s2@000000000000000010)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[0], bits["010000000000000000"], t8_1);
    info.eval->multiply_plain(ss[11], bits["000000000001000000"], t8_2);
    info.eval->multiply_plain(ss[14], bits["000000000000001000"], t8_3);
    info.eval->multiply_plain(ss[2], bits["000000000000000010"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__v1@010000000000000010, __s6@000000000001000000, __s4@000000000000001000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(vs[1], bits["010000000000000010"], t9_1);
    info.eval->multiply_plain(ss[6], bits["000000000001000000"], t9_2);
    info.eval->multiply_plain(ss[4], bits["000000000000001000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -4, gk, ss[20]); // __s20 = __v4 >> 4
    info.eval->rotate_rows(vs[4], -16, gk, ss[21]); // __s21 = __v4 >> 16
    info.eval->rotate_rows(vs[4], -13, gk, ss[22]); // __s22 = __v4 >> 13
    info.eval->multiply(vs[2], ss[6], vs[5]); // __v5 = __v2 * __s6
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t10 = blend(__s20@000001000000000000, __s18@000000100000000000, __s16@000000001000000000, __v3@000000000101000000, __s17@000000000000100000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(ss[20], bits["000001000000000000"], t10_1);
    info.eval->multiply_plain(ss[18], bits["000000100000000000"], t10_2);
    info.eval->multiply_plain(ss[16], bits["000000001000000000"], t10_3);
    info.eval->multiply_plain(vs[3], bits["000000000101000000"], t10_4);
    info.eval->multiply_plain(ss[17], bits["000000000000100000"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__s16@000001000000000000, __s17@000000101000000000, __s21@000000000100000000, __v5@000000000001000000, __v3@000000000000100000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5;
    info.eval->multiply_plain(ss[16], bits["000001000000000000"], t11_1);
    info.eval->multiply_plain(ss[17], bits["000000101000000000"], t11_2);
    info.eval->multiply_plain(ss[21], bits["000000000100000000"], t11_3);
    info.eval->multiply_plain(vs[5], bits["000000000001000000"], t11_4);
    info.eval->multiply_plain(vs[3], bits["000000000000100000"], t11_5);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[6]); // __v6 = __t10 + __t11
    info.eval->rotate_rows(vs[6], -17, gk, ss[23]); // __s23 = __v6 >> 17
    
    // __t12 = blend(__s22@000000000001000000, __s19@000000000000100000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[22], bits["000000000001000000"], t12_1);
    info.eval->multiply_plain(ss[19], bits["000000000000100000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__s19@000000000001000000, __s21@000000000000100000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[19], bits["000000000001000000"], t13_1);
    info.eval->multiply_plain(ss[21], bits["000000000000100000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[7]); // __v7 = __t12 + __t13
    info.eval->rotate_rows(vs[7], -11, gk, ss[24]); // __s24 = __v7 >> 11
    info.eval->multiply(vs[0], vs[7], vs[8]); // __v8 = __v0 * __v7
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t14 = blend(__s1@000001000000000000, __s0@000000001000000000, __s2@000000000010000000, __s13@000000000001000000)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(ss[1], bits["000001000000000000"], t14_1);
    info.eval->multiply_plain(ss[0], bits["000000001000000000"], t14_2);
    info.eval->multiply_plain(ss[2], bits["000000000010000000"], t14_3);
    info.eval->multiply_plain(ss[13], bits["000000000001000000"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    
    // __t15 = blend(__v6@000001000000000000, __s23@000000001011000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[6], bits["000001000000000000"], t15_1);
    info.eval->multiply_plain(ss[23], bits["000000001011000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[9]); // __v9 = __t14 * __t15
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -16, gk, ss[25]); // __s25 = __v9 >> 16
    
    // __t16 = blend(__s12@000001000000000000, __s11@000000001000000000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(ss[12], bits["000001000000000000"], t16_1);
    info.eval->multiply_plain(ss[11], bits["000000001000000000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__s24@000001000000000000, __v6@000000001000000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[24], bits["000001000000000000"], t17_1);
    info.eval->multiply_plain(vs[6], bits["000000001000000000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[10]); // __v10 = __t16 * __t17
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -16, gk, ss[26]); // __s26 = __v10 >> 16
    info.eval->multiply(ss[12], vs[6], vs[11]); // __v11 = __s12 * __v6
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t18 = blend(__s25@000100101000000000, __v8@000000000001000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[25], bits["000100101000000000"], t18_1);
    info.eval->multiply_plain(vs[8], bits["000000000001000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    
    // __t19 = blend(__s26@000100000000000000, __v11@000000100000000000, __v10@000000001000000000, __v9@000000000001000000)
    ctxt t19_1, t19_2, t19_3, t19_4;
    info.eval->multiply_plain(ss[26], bits["000100000000000000"], t19_1);
    info.eval->multiply_plain(vs[11], bits["000000100000000000"], t19_2);
    info.eval->multiply_plain(vs[10], bits["000000001000000000"], t19_3);
    info.eval->multiply_plain(vs[9], bits["000000000001000000"], t19_4);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[12]); // __v12 = __t18 + __t19
    info.eval->rotate_rows(vs[12], -13, gk, ss[27]); // __s27 = __v12 >> 13
    info.eval->multiply(ss[0], vs[12], vs[13]); // __v13 = __s0 * __v12
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->rotate_rows(vs[13], -13, gk, ss[28]); // __s28 = __v13 >> 13
    
    // __t20 = blend(__v2@000100000000000000, __s10@000000100000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[2], bits["000100000000000000"], t20_1);
    info.eval->multiply_plain(ss[10], bits["000000100000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__s27@000100000000000000, __v12@000000100000000000)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(ss[27], bits["000100000000000000"], t21_1);
    info.eval->multiply_plain(vs[12], bits["000000100000000000"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->multiply(ts[20], ts[21], vs[14]); // __v14 = __t20 * __t21
    info.eval->relinearize_inplace(vs[14], rk);
    
    // __t22 = blend(__v13@000100000000000000, __s28@000000100000000000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[13], bits["000100000000000000"], t22_1);
    info.eval->multiply_plain(ss[28], bits["000000100000000000"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);
    
    info.eval->add(ts[22], vs[14], vs[15]); // __v15 = __t22 + __v14
    info.eval->rotate_rows(vs[15], -3, gk, ss[29]); // __s29 = __v15 >> 3
    info.eval->multiply(ss[15], vs[15], vs[16]); // __v16 = __s15 * __v15
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->multiply(ss[3], ss[29], vs[17]); // __v17 = __s3 * __s29
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->add(vs[17], vs[16], vs[18]); // __v18 = __v17 + __v16
    return vs[18];
}
    