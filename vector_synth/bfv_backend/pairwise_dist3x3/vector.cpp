
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000100010", info);
    add_bitstring(bits, "0100000000", info);
    add_bitstring(bits, "0000100001", info);
    add_bitstring(bits, "0000000001", info);
    add_bitstring(bits, "0000010000", info);
    add_bitstring(bits, "0111001100", info);
    add_bitstring(bits, "0000110000", info);
    add_bitstring(bits, "0010001010", info);
    add_bitstring(bits, "0001000000", info);
    add_bitstring(bits, "1010001110", info);
    add_bitstring(bits, "0100000100", info);
    add_bitstring(bits, "0101100001", info);
    add_bitstring(bits, "0000100000", info);
    add_bitstring(bits, "0000001000", info);
    add_bitstring(bits, "0000001100", info);
    add_bitstring(bits, "0000100010", info);
    add_bitstring(bits, "0000000010", info);
    add_bitstring(bits, "1101100100", info);
    add_bitstring(bits, "0010000000", info);
    add_bitstring(bits, "1000000000", info);
    add_bitstring(bits, "0011000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(22);
    ts[0] = encrypt_input("0011111101100000", info);
    ts[2] = encrypt_input("0011111100000110", info);
    ts[4] = encrypt_input("0001111101110000", info);
    ts[6] = encrypt_input("0001111100000111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[14];
    ctxt ss[20];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -4, gk, ss[1]); // __s1 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -5, gk, ss[2]); // __s2 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -9, gk, ss[3]); // __s3 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -6, gk, ss[4]); // __s4 = __v0 >> 6
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -8, gk, ss[5]); // __s5 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -4, gk, ss[6]); // __s6 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -5, gk, ss[7]); // __s7 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -2, gk, ss[8]); // __s8 = __v1 >> 2
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -8, gk, ss[9]); // __s9 = __v2 >> 8
    info.eval->rotate_rows(vs[2], -9, gk, ss[10]); // __s10 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -2, gk, ss[11]); // __s11 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -4, gk, ss[12]); // __s12 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -5, gk, ss[13]); // __s13 = __v2 >> 5
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -8, gk, ss[14]); // __s14 = __v3 >> 8
    info.eval->rotate_rows(vs[3], -9, gk, ss[15]); // __s15 = __v3 >> 9
    info.eval->rotate_rows(vs[3], -2, gk, ss[16]); // __s16 = __v3 >> 2
    info.eval->rotate_rows(vs[3], -4, gk, ss[17]); // __s17 = __v3 >> 4
    info.eval->rotate_rows(vs[3], -1, gk, ss[18]); // __s18 = __v3 >> 1
    
    // __t8 = blend(__s5@1000000000, __s4@0100000000, __v0@0011000000, __s7@0000100010, __s1@0000001100, __v1@0000000001)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6;
    info.eval->multiply_plain(ss[5], bits["1000000000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["0100000000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["0011000000"], t8_3);
    info.eval->multiply_plain(ss[7], bits["0000100010"], t8_4);
    info.eval->multiply_plain(ss[1], bits["0000001100"], t8_5);
    info.eval->multiply_plain(vs[1], bits["0000000001"], t8_6);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6}, ts[8]);
    
    
    // __t9 = blend(__s18@1000000000, __s9@0100000000, __s10@0010000000, __v2@0001000000, __v3@0000100001, __s11@0000001100, __s17@0000000010)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7;
    info.eval->multiply_plain(ss[18], bits["1000000000"], t9_1);
    info.eval->multiply_plain(ss[9], bits["0100000000"], t9_2);
    info.eval->multiply_plain(ss[10], bits["0010000000"], t9_3);
    info.eval->multiply_plain(vs[2], bits["0001000000"], t9_4);
    info.eval->multiply_plain(vs[3], bits["0000100001"], t9_5);
    info.eval->multiply_plain(ss[11], bits["0000001100"], t9_6);
    info.eval->multiply_plain(ss[17], bits["0000000010"], t9_7);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t12 = blend(__v4@1010001110, __v4@0101100001)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[4], bits["1010001110"], t12_1);
    info.eval->multiply_plain(vs[4], bits["0101100001"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    info.eval->multiply(ts[12], ts[12], vs[6]); // __v6 = __t12 * __t12
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__s0@1000000000, __s8@0100000000, __v1@0011000000, __s3@0000100000, __v0@0000010000, __s6@0000001100, __s2@0000000010)
    ctxt t14_1, t14_2, t14_3, t14_4, t14_5, t14_6, t14_7;
    info.eval->multiply_plain(ss[0], bits["1000000000"], t14_1);
    info.eval->multiply_plain(ss[8], bits["0100000000"], t14_2);
    info.eval->multiply_plain(vs[1], bits["0011000000"], t14_3);
    info.eval->multiply_plain(ss[3], bits["0000100000"], t14_4);
    info.eval->multiply_plain(vs[0], bits["0000010000"], t14_5);
    info.eval->multiply_plain(ss[6], bits["0000001100"], t14_6);
    info.eval->multiply_plain(ss[2], bits["0000000010"], t14_7);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4, t14_5, t14_6, t14_7}, ts[14]);
    
    
    // __t15 = blend(__s13@1000000000, __s14@0100000100, __s15@0010000000, __v3@0001000000, __v2@0000110000, __s16@0000001000, __s12@0000000010)
    ctxt t15_1, t15_2, t15_3, t15_4, t15_5, t15_6, t15_7;
    info.eval->multiply_plain(ss[13], bits["1000000000"], t15_1);
    info.eval->multiply_plain(ss[14], bits["0100000100"], t15_2);
    info.eval->multiply_plain(ss[15], bits["0010000000"], t15_3);
    info.eval->multiply_plain(vs[3], bits["0001000000"], t15_4);
    info.eval->multiply_plain(vs[2], bits["0000110000"], t15_5);
    info.eval->multiply_plain(ss[16], bits["0000001000"], t15_6);
    info.eval->multiply_plain(ss[12], bits["0000000010"], t15_7);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4, t15_5, t15_6, t15_7}, ts[15]);
    
    info.eval->sub(ts[14], ts[15], vs[7]); // __v7 = __t14 - __t15
    
    // __t16 = blend(__s0@1000000000, __s8@0100000000, __v1@0011000000, __s3@0000100000, __s6@0000001100, __s2@0000000010)
    ctxt t16_1, t16_2, t16_3, t16_4, t16_5, t16_6;
    info.eval->multiply_plain(ss[0], bits["1000000000"], t16_1);
    info.eval->multiply_plain(ss[8], bits["0100000000"], t16_2);
    info.eval->multiply_plain(vs[1], bits["0011000000"], t16_3);
    info.eval->multiply_plain(ss[3], bits["0000100000"], t16_4);
    info.eval->multiply_plain(ss[6], bits["0000001100"], t16_5);
    info.eval->multiply_plain(ss[2], bits["0000000010"], t16_6);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, t16_5, t16_6}, ts[16]);
    
    
    // __t17 = blend(__s13@1000000000, __s14@0100000100, __s15@0010000000, __v3@0001000000, __v2@0000100000, __s16@0000001000, __s12@0000000010)
    ctxt t17_1, t17_2, t17_3, t17_4, t17_5, t17_6, t17_7;
    info.eval->multiply_plain(ss[13], bits["1000000000"], t17_1);
    info.eval->multiply_plain(ss[14], bits["0100000100"], t17_2);
    info.eval->multiply_plain(ss[15], bits["0010000000"], t17_3);
    info.eval->multiply_plain(vs[3], bits["0001000000"], t17_4);
    info.eval->multiply_plain(vs[2], bits["0000100000"], t17_5);
    info.eval->multiply_plain(ss[16], bits["0000001000"], t17_6);
    info.eval->multiply_plain(ss[12], bits["0000000010"], t17_7);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4, t17_5, t17_6, t17_7}, ts[17]);
    
    info.eval->sub(ts[16], ts[17], vs[8]); // __v8 = __t16 - __t17
    
    // __t18 = blend(__v8@1101100100, __v7@0010001010)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[8], bits["1101100100"], t18_1);
    info.eval->multiply_plain(vs[7], bits["0010001010"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    
    // __t19 = blend(__v7@1101100100, __v8@0010001010)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[7], bits["1101100100"], t19_1);
    info.eval->multiply_plain(vs[8], bits["0010001010"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[9]); // __v9 = __t18 * __t19
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t20 = blend(__v9@1000100010, __v6@0111001100)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[9], bits["1000100010"], t20_1);
    info.eval->multiply_plain(vs[6], bits["0111001100"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v6@1000100010, __v9@0111001100)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[6], bits["1000100010"], t21_1);
    info.eval->multiply_plain(vs[9], bits["0111001100"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[10]); // __v10 = __t20 + __t21
    info.eval->sub(vs[0], vs[2], vs[11]); // __v11 = __v0 - __v2
    info.eval->multiply(vs[11], vs[7], vs[12]); // __v12 = __v11 * __v7
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -4, gk, ss[19]); // __s19 = __v12 >> 4
    info.eval->add(ss[19], vs[6], vs[13]); // __v13 = __s19 + __v6
    return vs[13];
}
    