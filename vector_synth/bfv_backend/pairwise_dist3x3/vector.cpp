
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000010000000000000", info);
    add_bitstring(bits, "000000110000000000000", info);
    add_bitstring(bits, "000000010100010000001", info);
    add_bitstring(bits, "000000110000010000000", info);
    add_bitstring(bits, "000000000000010000000", info);
    add_bitstring(bits, "000000110000000000001", info);
    add_bitstring(bits, "000000000100000000001", info);
    add_bitstring(bits, "000000110010000010010", info);
    add_bitstring(bits, "000000010100000000001", info);
    add_bitstring(bits, "000000100000000000000", info);
    add_bitstring(bits, "000000000100010000001", info);
    add_bitstring(bits, "000000000010000010010", info);
    add_bitstring(bits, "000000000000000010000", info);
    add_bitstring(bits, "000000000000000000001", info);
    add_bitstring(bits, "000000000110000011010", info);
    add_bitstring(bits, "000000100010000011010", info);
    add_bitstring(bits, "000000100010000010010", info);
    add_bitstring(bits, "000000000000000000100", info);
    add_bitstring(bits, "000000000100000001001", info);
    add_bitstring(bits, "000000000000000000010", info);
    add_bitstring(bits, "000000000100000001100", info);
    add_bitstring(bits, "000000000100000000000", info);
    add_bitstring(bits, "000000000000000001100", info);
    add_bitstring(bits, "000000000010000000000", info);
    add_bitstring(bits, "000000000000000001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(22);
    ts[0] = encrypt_input("011111101101101111110110110111110111111111111110111111111", info);
    ts[2] = encrypt_input("011111101101101111111111101101111101111111111111100111111", info);
    ts[4] = encrypt_input("000000000011000000011111100", info);
    ts[6] = encrypt_input("111000000000110000000111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[16];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -5, gk, ss[0]); // __s0 = __v0 >> 5
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -5, gk, ss[1]); // __s1 = __v1 >> 5
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -17, gk, ss[2]); // __s2 = __v2 >> 17
    info.eval->rotate_rows(vs[2], -18, gk, ss[3]); // __s3 = __v2 >> 18
    info.eval->rotate_rows(vs[2], -2, gk, ss[4]); // __s4 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -3, gk, ss[5]); // __s5 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -19, gk, ss[6]); // __s6 = __v2 >> 19
    info.eval->rotate_rows(vs[2], -12, gk, ss[7]); // __s7 = __v2 >> 12
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -16, gk, ss[8]); // __s8 = __v3 >> 16
    info.eval->rotate_rows(vs[3], -9, gk, ss[9]); // __s9 = __v3 >> 9
    info.eval->rotate_rows(vs[3], -13, gk, ss[10]); // __s10 = __v3 >> 13
    info.eval->rotate_rows(vs[3], -17, gk, ss[11]); // __s11 = __v3 >> 17
    info.eval->rotate_rows(vs[3], -18, gk, ss[12]); // __s12 = __v3 >> 18
    info.eval->rotate_rows(vs[3], -2, gk, ss[13]); // __s13 = __v3 >> 2
    info.eval->rotate_rows(vs[3], -3, gk, ss[14]); // __s14 = __v3 >> 3
    
    // __t8 = blend(__v1@000000110000010000000, __s0@000000000100000001100, __s1@000000000010000010010, __v0@000000000000000000001)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[1], bits["000000110000010000000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["000000000100000001100"], t8_2);
    info.eval->multiply_plain(ss[1], bits["000000000010000010010"], t8_3);
    info.eval->multiply_plain(vs[0], bits["000000000000000000001"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s11@000000100000000000000, __s12@000000010000000000000, __s7@000000000100000000000, __v3@000000000010000000000, __s10@000000000000010000000, __s8@000000000000000010000, __v2@000000000000000001100, __s13@000000000000000000010, __s5@000000000000000000001)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7, t9_8, t9_9;
    info.eval->multiply_plain(ss[11], bits["000000100000000000000"], t9_1);
    info.eval->multiply_plain(ss[12], bits["000000010000000000000"], t9_2);
    info.eval->multiply_plain(ss[7], bits["000000000100000000000"], t9_3);
    info.eval->multiply_plain(vs[3], bits["000000000010000000000"], t9_4);
    info.eval->multiply_plain(ss[10], bits["000000000000010000000"], t9_5);
    info.eval->multiply_plain(ss[8], bits["000000000000000010000"], t9_6);
    info.eval->multiply_plain(vs[2], bits["000000000000000001100"], t9_7);
    info.eval->multiply_plain(ss[13], bits["000000000000000000010"], t9_8);
    info.eval->multiply_plain(ss[5], bits["000000000000000000001"], t9_9);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7, t9_8, t9_9}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__s1@000000110000000000000, __v0@000000000100000001100, __v1@000000000010000010010, __s0@000000000000000000001)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[1], bits["000000110000000000000"], t10_1);
    info.eval->multiply_plain(vs[0], bits["000000000100000001100"], t10_2);
    info.eval->multiply_plain(vs[1], bits["000000000010000010010"], t10_3);
    info.eval->multiply_plain(ss[0], bits["000000000000000000001"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s11@000000100000000000000, __s12@000000010000000000000, __s7@000000000100000000000, __v3@000000000010000000000, __s8@000000000000000010000, __v2@000000000000000001100, __s13@000000000000000000010, __s5@000000000000000000001)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7, t11_8;
    info.eval->multiply_plain(ss[11], bits["000000100000000000000"], t11_1);
    info.eval->multiply_plain(ss[12], bits["000000010000000000000"], t11_2);
    info.eval->multiply_plain(ss[7], bits["000000000100000000000"], t11_3);
    info.eval->multiply_plain(vs[3], bits["000000000010000000000"], t11_4);
    info.eval->multiply_plain(ss[8], bits["000000000000000010000"], t11_5);
    info.eval->multiply_plain(vs[2], bits["000000000000000001100"], t11_6);
    info.eval->multiply_plain(ss[13], bits["000000000000000000010"], t11_7);
    info.eval->multiply_plain(ss[5], bits["000000000000000000001"], t11_8);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7, t11_8}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v4@000000110000000000001, __v5@000000000110000011010)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[4], bits["000000110000000000001"], t12_1);
    info.eval->multiply_plain(vs[5], bits["000000000110000011010"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v5@000000110000000000001, __v4@000000000110000011010)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[5], bits["000000110000000000001"], t13_1);
    info.eval->multiply_plain(vs[4], bits["000000000110000011010"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__v0@000000100010000010010, __s0@000000010000000000000, __s1@000000000100010000001, __v1@000000000000000001000)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(vs[0], bits["000000100010000010010"], t14_1);
    info.eval->multiply_plain(ss[0], bits["000000010000000000000"], t14_2);
    info.eval->multiply_plain(ss[1], bits["000000000100010000001"], t14_3);
    info.eval->multiply_plain(vs[1], bits["000000000000000001000"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    
    // __t15 = blend(__s2@000000100000000000000, __s3@000000010000000000000, __s9@000000000100000000000, __v2@000000000010000000000, __s10@000000000000010000000, __s6@000000000000000010000, __v3@000000000000000001000, __s4@000000000000000000010, __s14@000000000000000000001)
    ctxt t15_1, t15_2, t15_3, t15_4, t15_5, t15_6, t15_7, t15_8, t15_9;
    info.eval->multiply_plain(ss[2], bits["000000100000000000000"], t15_1);
    info.eval->multiply_plain(ss[3], bits["000000010000000000000"], t15_2);
    info.eval->multiply_plain(ss[9], bits["000000000100000000000"], t15_3);
    info.eval->multiply_plain(vs[2], bits["000000000010000000000"], t15_4);
    info.eval->multiply_plain(ss[10], bits["000000000000010000000"], t15_5);
    info.eval->multiply_plain(ss[6], bits["000000000000000010000"], t15_6);
    info.eval->multiply_plain(vs[3], bits["000000000000000001000"], t15_7);
    info.eval->multiply_plain(ss[4], bits["000000000000000000010"], t15_8);
    info.eval->multiply_plain(ss[14], bits["000000000000000000001"], t15_9);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4, t15_5, t15_6, t15_7, t15_8, t15_9}, ts[15]);
    
    info.eval->sub(ts[14], ts[15], vs[7]); // __v7 = __t14 - __t15
    
    // __t16 = blend(__s0@000000100010000010010, __v0@000000010000000000000, __v1@000000000100000000001, __s1@000000000000000001000)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(ss[0], bits["000000100010000010010"], t16_1);
    info.eval->multiply_plain(vs[0], bits["000000010000000000000"], t16_2);
    info.eval->multiply_plain(vs[1], bits["000000000100000000001"], t16_3);
    info.eval->multiply_plain(ss[1], bits["000000000000000001000"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4}, ts[16]);
    
    
    // __t17 = blend(__s2@000000100000000000000, __s3@000000010000000000000, __s9@000000000100000000000, __v2@000000000010000000000, __s6@000000000000000010000, __v3@000000000000000001000, __s4@000000000000000000010, __s14@000000000000000000001)
    ctxt t17_1, t17_2, t17_3, t17_4, t17_5, t17_6, t17_7, t17_8;
    info.eval->multiply_plain(ss[2], bits["000000100000000000000"], t17_1);
    info.eval->multiply_plain(ss[3], bits["000000010000000000000"], t17_2);
    info.eval->multiply_plain(ss[9], bits["000000000100000000000"], t17_3);
    info.eval->multiply_plain(vs[2], bits["000000000010000000000"], t17_4);
    info.eval->multiply_plain(ss[6], bits["000000000000000010000"], t17_5);
    info.eval->multiply_plain(vs[3], bits["000000000000000001000"], t17_6);
    info.eval->multiply_plain(ss[4], bits["000000000000000000010"], t17_7);
    info.eval->multiply_plain(ss[14], bits["000000000000000000001"], t17_8);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4, t17_5, t17_6, t17_7, t17_8}, ts[17]);
    
    info.eval->sub(ts[16], ts[17], vs[8]); // __v8 = __t16 - __t17
    
    // __t18 = blend(__v7@000000100010000011010, __v8@000000010100000000001, __v4@000000000000010000000, __v5@000000000000000000100)
    ctxt t18_1, t18_2, t18_3, t18_4;
    info.eval->multiply_plain(vs[7], bits["000000100010000011010"], t18_1);
    info.eval->multiply_plain(vs[8], bits["000000010100000000001"], t18_2);
    info.eval->multiply_plain(vs[4], bits["000000000000010000000"], t18_3);
    info.eval->multiply_plain(vs[5], bits["000000000000000000100"], t18_4);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4}, ts[18]);
    
    
    // __t19 = blend(__v8@000000100010000011010, __v7@000000010100010000001, __v4@000000000000000000100)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[8], bits["000000100010000011010"], t19_1);
    info.eval->multiply_plain(vs[7], bits["000000010100010000001"], t19_2);
    info.eval->multiply_plain(vs[4], bits["000000000000000000100"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[9]); // __v9 = __t18 * __t19
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -5, gk, ss[15]); // __s15 = __v9 >> 5
    
    // __t20 = blend(__v9@000000110010000010010, __v6@000000000100000001001)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[9], bits["000000110010000010010"], t20_1);
    info.eval->multiply_plain(vs[6], bits["000000000100000001001"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v6@000000110010000010010, __v9@000000000100000001001)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[6], bits["000000110010000010010"], t21_1);
    info.eval->multiply_plain(vs[9], bits["000000000100000001001"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[10]); // __v10 = __t20 + __t21
    info.eval->add(vs[9], ss[15], vs[11]); // __v11 = __v9 + __s15
    return vs[11];
}
    