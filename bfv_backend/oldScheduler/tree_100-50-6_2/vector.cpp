
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000100000000000000000000000", info);
    add_bitstring(bits, "0000000000000001000000000000", info);
    add_bitstring(bits, "0000000000000000000100000000", info);
    add_bitstring(bits, "0000000000000000000010000000", info);
    add_bitstring(bits, "0010000000000000000000000000", info);
    add_bitstring(bits, "0000000000001000000000000000", info);
    add_bitstring(bits, "0000000000000010000000000000", info);
    add_bitstring(bits, "0001000000000000000000000000", info);
    add_bitstring(bits, "1000000000100010000100000000", info);
    add_bitstring(bits, "0000000000000000000001000000", info);
    add_bitstring(bits, "0001000010000000000000000000", info);
    add_bitstring(bits, "0000000000000000100000000000", info);
    add_bitstring(bits, "0000000000000010010010000000", info);
    add_bitstring(bits, "1000000000000000000100000000", info);
    add_bitstring(bits, "0000000000100010000000000000", info);
    add_bitstring(bits, "0000000000000000010000000000", info);
    add_bitstring(bits, "0000000010000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(30);
    ts[0] = encrypt_input("110000000111000110001110001111110000000", info);
    ts[1] = encrypt_input("11000000011100011100110001101110000000", info);
    ts[2] = encrypt_input("1011011000011000111011101110000110111000000", info);
    ts[3] = encrypt_input("11101110000110001110111011000001010111000000", info);
    ts[4] = encrypt_input("000001110001111110001110000000111000111111", info);
    ts[5] = encrypt_input("0000010100011111100011100000001110001011111", info);
    ts[8] = encrypt_input("000110110000000111000000000000011100", info);
    ts[9] = encrypt_input("00010111000000111000000000000011100", info);
    ts[12] = encrypt_input("001000000000000011100000000000", info);
    ts[13] = encrypt_input("00111000000000000011100000000000", info);
    ts[14] = encrypt_input("0000000000000011100111001110000000", info);
    ts[15] = encrypt_input("000000000000001110011001100000000", info);
    ts[20] = encrypt_input("00000000101000000000000111000000", info);
    ts[21] = encrypt_input("000000001010000000000000111000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[17];
    ctxt ss[16];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -22, gk, ss[0]); // __s0 = __v0 >> 22
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->rotate_rows(vs[1], -12, gk, ss[1]); // __s1 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -22, gk, ss[2]); // __s2 = __v1 >> 22
    
    // __t6 = blend(__v1@0000000000001000000000000000, __t4@0000010001100010000000100011)
    ctxt t6_1;
    info.eval->multiply_plain(vs[1], bits["0000000000001000000000000000"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@0000000000001000000000000000, __t5@0000010001100010000000100011)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["0000000000001000000000000000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -12, gk, ss[3]); // __s3 = __v2 >> 12
    info.eval->rotate_rows(vs[2], -22, gk, ss[4]); // __s4 = __v2 >> 22
    
    // __t10 = blend(__v0@1000000000000000000100000000, __v2@0000000000100010000000000000, __t8@0001100000010000000000000100)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[0], bits["1000000000000000000100000000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["0000000000100010000000000000"], t10_2);
    info.eval->add_many({t10_1, t10_2, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__v1@1000000000100010000100000000, __t9@0001100000010000000000000100)
    ctxt t11_1;
    info.eval->multiply_plain(vs[1], bits["1000000000100010000100000000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -12, gk, ss[5]); // __s5 = __v3 >> 12
    info.eval->rotate_rows(vs[3], -21, gk, ss[6]); // __s6 = __v3 >> 21
    info.eval->rotate_rows(vs[3], -22, gk, ss[7]); // __s7 = __v3 >> 22
    info.eval->add(ts[12], ts[13], vs[4]); // __v4 = __t12 + __t13
    
    // __t16 = blend(__v3@0000100000000000000000000000, __v2@0000000000001000000000000000, __v0@0000000000000001000000000000, __t14@0000000000000010010010000000)
    ctxt t16_1, t16_2, t16_3;
    info.eval->multiply_plain(vs[3], bits["0000100000000000000000000000"], t16_1);
    info.eval->multiply_plain(vs[2], bits["0000000000001000000000000000"], t16_2);
    info.eval->multiply_plain(vs[0], bits["0000000000000001000000000000"], t16_3);
    info.eval->add_many({t16_1, t16_2, t16_3, ts[14]}, ts[16]);
    
    
    // __t17 = blend(__s6@0000100000000000000000000000, __s5@0000000000001000000000000000, __s2@0000000000000001000000000000, __t15@0000000000000010010010000000)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(ss[6], bits["0000100000000000000000000000"], t17_1);
    info.eval->multiply_plain(ss[5], bits["0000000000001000000000000000"], t17_2);
    info.eval->multiply_plain(ss[2], bits["0000000000000001000000000000"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3, ts[15]}, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[5]); // __v5 = __t16 * __t17
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -27, gk, ss[8]); // __s8 = __v5 >> 27
    info.eval->rotate_rows(vs[5], -24, gk, ss[9]); // __s9 = __v5 >> 24
    
    // __t18 = blend(__v4@0010000000000000000000000000, __v5@0000000000000010010010000000, __s4@0000000000000000100000000000, __s7@0000000000000000000100000000)
    ctxt t18_1, t18_2, t18_3, t18_4;
    info.eval->multiply_plain(vs[4], bits["0010000000000000000000000000"], t18_1);
    info.eval->multiply_plain(vs[5], bits["0000000000000010010010000000"], t18_2);
    info.eval->multiply_plain(ss[4], bits["0000000000000000100000000000"], t18_3);
    info.eval->multiply_plain(ss[7], bits["0000000000000000000100000000"], t18_4);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4}, ts[18]);
    
    
    // __t19 = blend(__v1@0010000000000000000000000000, __s0@0000000000000010000000000000, __v4@0000000000000000100000000000, __s3@0000000000000000010000000000, __s1@0000000000000000000100000000, __s4@0000000000000000000010000000)
    ctxt t19_1, t19_2, t19_3, t19_4, t19_5, t19_6;
    info.eval->multiply_plain(vs[1], bits["0010000000000000000000000000"], t19_1);
    info.eval->multiply_plain(ss[0], bits["0000000000000010000000000000"], t19_2);
    info.eval->multiply_plain(vs[4], bits["0000000000000000100000000000"], t19_3);
    info.eval->multiply_plain(ss[3], bits["0000000000000000010000000000"], t19_4);
    info.eval->multiply_plain(ss[1], bits["0000000000000000000100000000"], t19_5);
    info.eval->multiply_plain(ss[4], bits["0000000000000000000010000000"], t19_6);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4, t19_5, t19_6}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[6]); // __v6 = __t18 + __t19
    info.eval->rotate_rows(vs[6], -1, gk, ss[10]); // __s10 = __v6 >> 1
    info.eval->rotate_rows(vs[6], -27, gk, ss[11]); // __s11 = __v6 >> 27
    info.eval->multiply(ts[20], ts[21], vs[7]); // __v7 = __t20 * __t21
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t22 = blend(__v3@0001000000000000000000000000, __v7@0000000010000000000000000000, __s11@0000000000000000100000000000, __s4@0000000000000000000001000000)
    ctxt t22_1, t22_2, t22_3, t22_4;
    info.eval->multiply_plain(vs[3], bits["0001000000000000000000000000"], t22_1);
    info.eval->multiply_plain(vs[7], bits["0000000010000000000000000000"], t22_2);
    info.eval->multiply_plain(ss[11], bits["0000000000000000100000000000"], t22_3);
    info.eval->multiply_plain(ss[4], bits["0000000000000000000001000000"], t22_4);
    info.eval->add_many({t22_1, t22_2, t22_3, t22_4}, ts[22]);
    
    
    // __t23 = blend(__s4@0001000000000000000000000000, __v0@0000000010000000000000000000, __v6@0000000000000000100000000000, __v7@0000000000000000000001000000)
    ctxt t23_1, t23_2, t23_3, t23_4;
    info.eval->multiply_plain(ss[4], bits["0001000000000000000000000000"], t23_1);
    info.eval->multiply_plain(vs[0], bits["0000000010000000000000000000"], t23_2);
    info.eval->multiply_plain(vs[6], bits["0000000000000000100000000000"], t23_3);
    info.eval->multiply_plain(vs[7], bits["0000000000000000000001000000"], t23_4);
    info.eval->add_many({t23_1, t23_2, t23_3, t23_4}, ts[23]);
    
    info.eval->add(ts[22], ts[23], vs[8]); // __v8 = __t22 + __t23
    
    // __t24 = blend(__v8@0001000010000000000000000000, __v6@0000000000000000000100000000, __s10@0000000000000000000001000000)
    ctxt t24_1, t24_2, t24_3;
    info.eval->multiply_plain(vs[8], bits["0001000010000000000000000000"], t24_1);
    info.eval->multiply_plain(vs[6], bits["0000000000000000000100000000"], t24_2);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000001000000"], t24_3);
    info.eval->add_many({t24_1, t24_2, t24_3}, ts[24]);
    
    
    // __t25 = blend(__s8@0001000000000000000000000000, __s7@0000000010000000000000000000, __v3@0000000000000000000100000000, __v8@0000000000000000000001000000)
    ctxt t25_1, t25_2, t25_3, t25_4;
    info.eval->multiply_plain(ss[8], bits["0001000000000000000000000000"], t25_1);
    info.eval->multiply_plain(ss[7], bits["0000000010000000000000000000"], t25_2);
    info.eval->multiply_plain(vs[3], bits["0000000000000000000100000000"], t25_3);
    info.eval->multiply_plain(vs[8], bits["0000000000000000000001000000"], t25_4);
    info.eval->add_many({t25_1, t25_2, t25_3, t25_4}, ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[9]); // __v9 = __t24 * __t25
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -23, gk, ss[12]); // __s12 = __v9 >> 23
    info.eval->add(ss[9], vs[9], vs[10]); // __v10 = __s9 + __v9
    info.eval->rotate_rows(vs[10], -23, gk, ss[13]); // __s13 = __v10 >> 23
    
    // __t26 = blend(__s10@0001000000000000000000000000, __s12@0000000000000000100000000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(ss[10], bits["0001000000000000000000000000"], t26_1);
    info.eval->multiply_plain(ss[12], bits["0000000000000000100000000000"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__s6@0001000000000000000000000000, __v8@0000000000000000100000000000)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(ss[6], bits["0001000000000000000000000000"], t27_1);
    info.eval->multiply_plain(vs[8], bits["0000000000000000100000000000"], t27_2);
    info.eval->add(t27_1, t27_2, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[11]); // __v11 = __t26 * __t27
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -15, gk, ss[14]); // __s14 = __v11 >> 15
    
    // __t28 = blend(__v11@0001000000000000000000000000, __s8@0000000000000010000000000000)
    ctxt t28_1, t28_2;
    info.eval->multiply_plain(vs[11], bits["0001000000000000000000000000"], t28_1);
    info.eval->multiply_plain(ss[8], bits["0000000000000010000000000000"], t28_2);
    info.eval->add(t28_1, t28_2, ts[28]);
    
    
    // __t29 = blend(__v9@0001000000000000000000000000, __v6@0000000000000010000000000000)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(vs[9], bits["0001000000000000000000000000"], t29_1);
    info.eval->multiply_plain(vs[6], bits["0000000000000010000000000000"], t29_2);
    info.eval->add(t29_1, t29_2, ts[29]);
    
    info.eval->add(ts[28], ts[29], vs[12]); // __v12 = __t28 + __t29
    info.eval->multiply(vs[12], ss[12], vs[13]); // __v13 = __v12 * __s12
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->rotate_rows(vs[13], -17, gk, ss[15]); // __s15 = __v13 >> 17
    info.eval->add(vs[12], ss[13], vs[14]); // __v14 = __v12 + __s13
    info.eval->multiply(ss[14], ss[15], vs[15]); // __v15 = __s14 * __s15
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->multiply(vs[15], vs[14], vs[16]); // __v16 = __v15 * __v14
    info.eval->relinearize_inplace(vs[16], rk);
    return vs[16];
}
    