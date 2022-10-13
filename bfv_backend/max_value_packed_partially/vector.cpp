
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000100000000", info);
    add_bitstring(bits, "1100000011000000", info);
    add_bitstring(bits, "0000000000000001", info);
    add_bitstring(bits, "0000000000100000", info);
    add_bitstring(bits, "0001000100000000", info);
    add_bitstring(bits, "0010001000000000", info);
    add_bitstring(bits, "0100000001000000", info);
    add_bitstring(bits, "0000010000000000", info);
    add_bitstring(bits, "0000000001000000", info);
    add_bitstring(bits, "0000000000010000", info);
    add_bitstring(bits, "0011100000100110", info);
    add_bitstring(bits, "0100100000100000", info);
    add_bitstring(bits, "0001001000001000", info);
    add_bitstring(bits, "0011000000001000", info);
    add_bitstring(bits, "0001001101001000", info);
    add_bitstring(bits, "0001000000100000", info);
    add_bitstring(bits, "0000001000000000", info);
    add_bitstring(bits, "0001000000000000", info);
    add_bitstring(bits, "0100000000000000", info);
    add_bitstring(bits, "0000011000000000", info);
    add_bitstring(bits, "0100000101000000", info);
    add_bitstring(bits, "0000010000010000", info);
    add_bitstring(bits, "0010000000000000", info);
    add_bitstring(bits, "0000000000001000", info);
    add_bitstring(bits, "0011000100000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(20);
    ts[0] = encrypt_input("1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("000111111111111111111111111111111110011111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111111111111111111111111111111111111111111100", info);
    ts[3] = encrypt_input("000111111111111111111111111111111110011111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111111111111111111111111111111111111111111100", info);
    ts[4] = encrypt_input("1111110111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[16];
    ctxt ss[27];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -5, gk, ss[0]); // __s0 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -15, gk, ss[1]); // __s1 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -12, gk, ss[2]); // __s2 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -9, gk, ss[3]); // __s3 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -14, gk, ss[4]); // __s4 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -2, gk, ss[5]); // __s5 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -15, gk, ss[6]); // __s6 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -1, gk, ss[7]); // __s7 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -3, gk, ss[8]); // __s8 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -5, gk, ss[9]); // __s9 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -6, gk, ss[10]); // __s10 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -12, gk, ss[11]); // __s11 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -13, gk, ss[12]); // __s12 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -14, gk, ss[13]); // __s13 = __v1 >> 14
    
    // __t5 = blend(__v0@1100000011000000, __s1@0011100000100110, __s4@0000010000010000, __s0@0000000100000000, __s5@0000000000001000, __s3@0000000000000001)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6;
    info.eval->multiply_plain(vs[0], bits["1100000011000000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["0011100000100110"], t5_2);
    info.eval->multiply_plain(ss[4], bits["0000010000010000"], t5_3);
    info.eval->multiply_plain(ss[0], bits["0000000100000000"], t5_4);
    info.eval->multiply_plain(ss[5], bits["0000000000001000"], t5_5);
    info.eval->multiply_plain(ss[3], bits["0000000000000001"], t5_6);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6}, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->rotate_rows(vs[2], -5, gk, ss[14]); // __s14 = __v2 >> 5
    info.eval->rotate_rows(vs[2], -13, gk, ss[15]); // __s15 = __v2 >> 13
    info.eval->rotate_rows(vs[2], -14, gk, ss[16]); // __s16 = __v2 >> 14
    info.eval->rotate_rows(vs[2], -15, gk, ss[17]); // __s17 = __v2 >> 15
    info.eval->rotate_rows(vs[2], -1, gk, ss[18]); // __s18 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -12, gk, ss[19]); // __s19 = __v2 >> 12
    
    // __t6 = blend(__v2@0011000100000000, __s14@0000011000000000, __s19@0000000001000000, __s2@0000000000100000, __s15@0000000000010000, __s18@0000000000001000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(vs[2], bits["0011000100000000"], t6_1);
    info.eval->multiply_plain(ss[14], bits["0000011000000000"], t6_2);
    info.eval->multiply_plain(ss[19], bits["0000000001000000"], t6_3);
    info.eval->multiply_plain(ss[2], bits["0000000000100000"], t6_4);
    info.eval->multiply_plain(ss[15], bits["0000000000010000"], t6_5);
    info.eval->multiply_plain(ss[18], bits["0000000000001000"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6}, ts[6]);
    
    
    // __t7 = blend(__s11@0010000000000000, __s12@0001000000100000, __s6@0000010000000000, __v1@0000001000000000, __s7@0000000100000000, __s8@0000000001000000, __s9@0000000000010000, __s10@0000000000001000)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8;
    info.eval->multiply_plain(ss[11], bits["0010000000000000"], t7_1);
    info.eval->multiply_plain(ss[12], bits["0001000000100000"], t7_2);
    info.eval->multiply_plain(ss[6], bits["0000010000000000"], t7_3);
    info.eval->multiply_plain(vs[1], bits["0000001000000000"], t7_4);
    info.eval->multiply_plain(ss[7], bits["0000000100000000"], t7_5);
    info.eval->multiply_plain(ss[8], bits["0000000001000000"], t7_6);
    info.eval->multiply_plain(ss[9], bits["0000000000010000"], t7_7);
    info.eval->multiply_plain(ss[10], bits["0000000000001000"], t7_8);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -15, gk, ss[20]); // __s20 = __v3 >> 15
    
    // __t8 = blend(__s1@0011000000001000, __s0@0000011000000000, __s2@0000000000010000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[1], bits["0011000000001000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["0000011000000000"], t8_2);
    info.eval->multiply_plain(ss[2], bits["0000000000010000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s6@0010001000000000, __v1@0001000000000000, __s13@0000010000000000, __s12@0000000000010000, __s9@0000000000001000)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5;
    info.eval->multiply_plain(ss[6], bits["0010001000000000"], t9_1);
    info.eval->multiply_plain(vs[1], bits["0001000000000000"], t9_2);
    info.eval->multiply_plain(ss[13], bits["0000010000000000"], t9_3);
    info.eval->multiply_plain(ss[12], bits["0000000000010000"], t9_4);
    info.eval->multiply_plain(ss[9], bits["0000000000001000"], t9_5);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -15, gk, ss[21]); // __s21 = __v4 >> 15
    info.eval->multiply(ss[0], vs[1], vs[5]); // __v5 = __s0 * __v1
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t10 = blend(__s21@0100100000100000, __v4@0001001000001000, __v5@0000000100000000, __s20@0000000001000000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[21], bits["0100100000100000"], t10_1);
    info.eval->multiply_plain(vs[4], bits["0001001000001000"], t10_2);
    info.eval->multiply_plain(vs[5], bits["0000000100000000"], t10_3);
    info.eval->multiply_plain(ss[20], bits["0000000001000000"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s20@0100100000100000, __v3@0001001101001000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(ss[20], bits["0100100000100000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["0001001101001000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[6]); // __v6 = __t10 + __t11
    info.eval->rotate_rows(vs[6], -13, gk, ss[22]); // __s22 = __v6 >> 13
    
    // __t12 = blend(__s15@0100000000000000, __s2@0001000000000000, __s1@0000000100000000, __s17@0000000001000000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[15], bits["0100000000000000"], t12_1);
    info.eval->multiply_plain(ss[2], bits["0001000000000000"], t12_2);
    info.eval->multiply_plain(ss[1], bits["0000000100000000"], t12_3);
    info.eval->multiply_plain(ss[17], bits["0000000001000000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__s22@0100000101000000, __v6@0001000000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[22], bits["0100000101000000"], t13_1);
    info.eval->multiply_plain(vs[6], bits["0001000000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[7]); // __v7 = __t12 * __t13
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t14 = blend(__s2@0100000000000000, __s16@0001000000000000, __s17@0000000100000000, __s4@0000000001000000)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(ss[2], bits["0100000000000000"], t14_1);
    info.eval->multiply_plain(ss[16], bits["0001000000000000"], t14_2);
    info.eval->multiply_plain(ss[17], bits["0000000100000000"], t14_3);
    info.eval->multiply_plain(ss[4], bits["0000000001000000"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    
    // __t15 = blend(__v6@0100000101000000, __s22@0001000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[6], bits["0100000101000000"], t15_1);
    info.eval->multiply_plain(ss[22], bits["0001000000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[8]); // __v8 = __t14 * __t15
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t16 = blend(__v8@0100000001000000, __v7@0001000100000000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(vs[8], bits["0100000001000000"], t16_1);
    info.eval->multiply_plain(vs[7], bits["0001000100000000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__v7@0100000001000000, __v8@0001000100000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[7], bits["0100000001000000"], t17_1);
    info.eval->multiply_plain(vs[8], bits["0001000100000000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[9]); // __v9 = __t16 + __t17
    info.eval->rotate_rows(vs[9], -6, gk, ss[23]); // __s23 = __v9 >> 6
    
    // __t18 = blend(__s4@0000000100000000, __s1@0000000001000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[4], bits["0000000100000000"], t18_1);
    info.eval->multiply_plain(ss[1], bits["0000000001000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(ts[18], vs[9], vs[10]); // __v10 = __t18 * __v9
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -4, gk, ss[24]); // __s24 = __v10 >> 4
    
    // __t19 = blend(__s16@0000000100000000, __s15@0000000001000000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(ss[16], bits["0000000100000000"], t19_1);
    info.eval->multiply_plain(ss[15], bits["0000000001000000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    info.eval->multiply(ts[19], ss[23], vs[11]); // __v11 = __t19 * __s23
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -4, gk, ss[25]); // __s25 = __v11 >> 4
    info.eval->add(ss[24], ss[25], vs[12]); // __v12 = __s24 + __s25
    info.eval->multiply(ss[16], vs[12], vs[13]); // __v13 = __s16 * __v12
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->multiply(ss[0], vs[12], vs[14]); // __v14 = __s0 * __v12
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -2, gk, ss[26]); // __s26 = __v14 >> 2
    info.eval->add(ss[26], vs[13], vs[15]); // __v15 = __s26 + __v13
    return vs[15];
}
    