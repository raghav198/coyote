
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000000000000100000", info);
    add_bitstring(bits, "0000010000000000000000", info);
    add_bitstring(bits, "1000000000000000000000", info);
    add_bitstring(bits, "0000100000000000000000", info);
    add_bitstring(bits, "0000000100000000000000", info);
    add_bitstring(bits, "0100000000000000000000", info);
    add_bitstring(bits, "0000000000010000000000", info);
    add_bitstring(bits, "1000010000000000000000", info);
    add_bitstring(bits, "0110000000000000000000", info);
    add_bitstring(bits, "0001000000000000001000", info);
    add_bitstring(bits, "0000000000000000001000", info);
    add_bitstring(bits, "0000000000000000010000", info);
    add_bitstring(bits, "0001000000000000000000", info);
    add_bitstring(bits, "0000000000001000000000", info);
    add_bitstring(bits, "0000000000000001000000", info);
    add_bitstring(bits, "0010000000000000000000", info);
    add_bitstring(bits, "1000000000000001000000", info);
    add_bitstring(bits, "0000000000000010000000", info);
    add_bitstring(bits, "0000000000000100000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(40);
    ts[0] = encrypt_input("0111110101111111101011100001111110111111111101111111", info);
    ts[1] = encrypt_input("0111111110111110110011100001111100111111111101111111", info);
    ts[2] = encrypt_input("11100001110111011111111111000111000000", info);
    ts[3] = encrypt_input("111010100001110101111111011100111000000", info);
    ts[6] = encrypt_input("011111100000000001111110000000", info);
    ts[7] = encrypt_input("0000111000000011100000111000", info);
    ts[10] = encrypt_input("000000000000000111000000", info);
    ts[13] = encrypt_input("111000000000000000000000", info);
    ts[14] = encrypt_input("00000001110000000111000000", info);
    ts[17] = encrypt_input("000000011100000000000000", info);
    ts[18] = encrypt_input("000000000001110000000000", info);
    ts[21] = encrypt_input("011100000000000000000000", info);
    ts[28] = encrypt_input("000000000000101000000000", info);
    ts[31] = encrypt_input("000000000000000001000000", info);
    ts[32] = encrypt_input("000000000001110000000000", info);
    ts[35] = encrypt_input("000000000000111000000000", info);
    ts[36] = encrypt_input("00000000000000000010000", info);
    ts[37] = encrypt_input("000000000000111000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[18];
    ctxt ss[16];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -21, gk, ss[0]); // __s0 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -14, gk, ss[1]); // __s1 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -18, gk, ss[2]); // __s2 = __v0 >> 18
    
    // __t4 = blend(__v0@0010000000000000000000, __t2@1000010101111001000000)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["0010000000000000000000"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    
    // __t5 = blend(__v0@0000010000000000000000, __t3@1010000101111001000000)
    ctxt t5_1;
    info.eval->multiply_plain(vs[0], bits["0000010000000000000000"], t5_1);
    info.eval->add(t5_1, ts[3], ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[1]); // __v1 = __t4 + __t5
    info.eval->rotate_rows(vs[1], -14, gk, ss[3]); // __s3 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -18, gk, ss[4]); // __s4 = __v1 >> 18
    
    // __t8 = blend(__s0@0001000000000000001000, __s3@0000100000000000000000, __s4@0000000100000000000000, __s2@0000000000001000000000, __t6@0110000000000110000000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[0], bits["0001000000000000001000"], t8_1);
    info.eval->multiply_plain(ss[3], bits["0000100000000000000000"], t8_2);
    info.eval->multiply_plain(ss[4], bits["0000000100000000000000"], t8_3);
    info.eval->multiply_plain(ss[2], bits["0000000000001000000000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, ts[6]}, ts[8]);
    
    
    // __t9 = blend(__s3@0110000000000000000000, __v0@0001000000000000000000, __s0@0000000100000000000000, __s1@0000000000000100000000, __s2@0000000000000010000000, __t7@0000100000001000001000)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5;
    info.eval->multiply_plain(ss[3], bits["0110000000000000000000"], t9_1);
    info.eval->multiply_plain(vs[0], bits["0001000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[0], bits["0000000100000000000000"], t9_3);
    info.eval->multiply_plain(ss[1], bits["0000000000000100000000"], t9_4);
    info.eval->multiply_plain(ss[2], bits["0000000000000010000000"], t9_5);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, ts[7]}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[2]); // __v2 = __t8 + __t9
    info.eval->rotate_rows(vs[2], -20, gk, ss[5]); // __s5 = __v2 >> 20
    info.eval->rotate_rows(vs[2], -2, gk, ss[6]); // __s6 = __v2 >> 2
    
    // __t11 = blend(__v1@1000000000000001000000, __s1@0000010000000000000000, __s0@0000000000000000100000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[1], bits["1000000000000001000000"], t11_1);
    info.eval->multiply_plain(ss[1], bits["0000010000000000000000"], t11_2);
    info.eval->multiply_plain(ss[0], bits["0000000000000000100000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    
    // __t12 = blend(__s0@1000010000000000000000, __s2@0000000000000000100000, __t10@0000000000000001000000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[0], bits["1000010000000000000000"], t12_1);
    info.eval->multiply_plain(ss[2], bits["0000000000000000100000"], t12_2);
    info.eval->add_many({t12_1, t12_2, ts[10]}, ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[3]); // __v3 = __t11 * __t12
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -2, gk, ss[7]); // __s7 = __v3 >> 2
    
    // __t15 = blend(__s5@0110000000000000000000, __v2@0000000100000000000000, __v3@0000000000000001000000, __s6@0000000000000000100000, __t13@1000000000000000000000)
    ctxt t15_1, t15_2, t15_3, t15_4;
    info.eval->multiply_plain(ss[5], bits["0110000000000000000000"], t15_1);
    info.eval->multiply_plain(vs[2], bits["0000000100000000000000"], t15_2);
    info.eval->multiply_plain(vs[3], bits["0000000000000001000000"], t15_3);
    info.eval->multiply_plain(ss[6], bits["0000000000000000100000"], t15_4);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4, ts[13]}, ts[15]);
    
    
    // __t16 = blend(__s5@1000000000000000000000, __v2@0100000000000000000000, __v1@0010000000000000000000, __v3@0000000000000000100000, __t14@0000000100000001000000)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(ss[5], bits["1000000000000000000000"], t16_1);
    info.eval->multiply_plain(vs[2], bits["0100000000000000000000"], t16_2);
    info.eval->multiply_plain(vs[1], bits["0010000000000000000000"], t16_3);
    info.eval->multiply_plain(vs[3], bits["0000000000000000100000"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, ts[14]}, ts[16]);
    
    info.eval->add(ts[15], ts[16], vs[4]); // __v4 = __t15 + __t16
    info.eval->rotate_rows(vs[4], -1, gk, ss[8]); // __s8 = __v4 >> 1
    info.eval->rotate_rows(vs[4], -2, gk, ss[9]); // __s9 = __v4 >> 2
    info.eval->add(vs[4], ts[17], vs[5]); // __v5 = __v4 + __t17
    
    // __t19 = blend(__v3@0000010000000000000000, __s5@0000000000010000000000, __v0@0000000000000010000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[3], bits["0000010000000000000000"], t19_1);
    info.eval->multiply_plain(ss[5], bits["0000000000010000000000"], t19_2);
    info.eval->multiply_plain(vs[0], bits["0000000000000010000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    
    // __t20 = blend(__v1@0000010000000000000000, __s6@0000000000000010000000, __t18@0000000000010000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[1], bits["0000010000000000000000"], t20_1);
    info.eval->multiply_plain(ss[6], bits["0000000000000010000000"], t20_2);
    info.eval->add_many({t20_1, t20_2, ts[18]}, ts[20]);
    
    info.eval->multiply(ts[19], ts[20], vs[6]); // __v6 = __t19 * __t20
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -2, gk, ss[10]); // __s10 = __v6 >> 2
    
    // __t22 = blend(__v4@0000000000000000100000, __t21@0100000000000000000000)
    ctxt t22_1;
    info.eval->multiply_plain(vs[4], bits["0000000000000000100000"], t22_1);
    info.eval->add(t22_1, ts[21], ts[22]);
    
    
    // __t23 = blend(__s8@0100000000000000000000, __s10@0000000000000000100000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(ss[8], bits["0100000000000000000000"], t23_1);
    info.eval->multiply_plain(ss[10], bits["0000000000000000100000"], t23_2);
    info.eval->add(t23_1, t23_2, ts[23]);
    
    info.eval->add(ts[22], ts[23], vs[7]); // __v7 = __t22 + __t23
    info.eval->rotate_rows(vs[7], -7, gk, ss[11]); // __s11 = __v7 >> 7
    
    // __t24 = blend(__s8@0010000000000000000000, __v1@0000000100000000000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(ss[8], bits["0010000000000000000000"], t24_1);
    info.eval->multiply_plain(vs[1], bits["0000000100000000000000"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    
    // __t25 = blend(__v4@0010000000000000000000, __s10@0000000100000000000000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(vs[4], bits["0010000000000000000000"], t25_1);
    info.eval->multiply_plain(ss[10], bits["0000000100000000000000"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[8]); // __v8 = __t24 * __t25
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(ss[7], vs[8], vs[9]); // __v9 = __s7 + __v8
    info.eval->rotate_rows(vs[9], -10, gk, ss[12]); // __s12 = __v9 >> 10
    
    // __t26 = blend(__s11@0100000000000000000000, __v8@0000000100000000000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(ss[11], bits["0100000000000000000000"], t26_1);
    info.eval->multiply_plain(vs[8], bits["0000000100000000000000"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__v7@0100000000000000000000, __v5@0000000100000000000000)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(vs[7], bits["0100000000000000000000"], t27_1);
    info.eval->multiply_plain(vs[5], bits["0000000100000000000000"], t27_2);
    info.eval->add(t27_1, t27_2, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[10]); // __v10 = __t26 * __t27
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -10, gk, ss[13]); // __s13 = __v10 >> 10
    
    // __t29 = blend(__v6@0000000000010000000000, __s12@0000000000001000000000, __s13@0000000000000000010000)
    ctxt t29_1, t29_2, t29_3;
    info.eval->multiply_plain(vs[6], bits["0000000000010000000000"], t29_1);
    info.eval->multiply_plain(ss[12], bits["0000000000001000000000"], t29_2);
    info.eval->multiply_plain(ss[13], bits["0000000000000000010000"], t29_3);
    info.eval->add_many({t29_1, t29_2, t29_3}, ts[29]);
    
    
    // __t30 = blend(__s13@0000000000010000000000, __s9@0000000000000000010000, __t28@0000000000001000000000)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(ss[13], bits["0000000000010000000000"], t30_1);
    info.eval->multiply_plain(ss[9], bits["0000000000000000010000"], t30_2);
    info.eval->add_many({t30_1, t30_2, ts[28]}, ts[30]);
    
    info.eval->multiply(ts[29], ts[30], vs[11]); // __v11 = __t29 * __t30
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t33 = blend(__v11@0000000000010000000000, __t31@0000000000000000010000)
    ctxt t33_1;
    info.eval->multiply_plain(vs[11], bits["0000000000010000000000"], t33_1);
    info.eval->add(t33_1, ts[31], ts[33]);
    
    
    // __t34 = blend(__v11@0000000000000000010000, __t32@0000000000010000000000)
    ctxt t34_1;
    info.eval->multiply_plain(vs[11], bits["0000000000000000010000"], t34_1);
    info.eval->add(t34_1, ts[32], ts[34]);
    
    info.eval->multiply(ts[33], ts[34], vs[12]); // __v12 = __t33 * __t34
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -1, gk, ss[14]); // __s14 = __v12 >> 1
    info.eval->add(vs[11], ts[35], vs[13]); // __v13 = __v11 + __t35
    info.eval->add(vs[13], ss[14], vs[14]); // __v14 = __v13 + __s14
    info.eval->multiply(ss[14], ts[36], vs[15]); // __v15 = __s14 * __t36
    info.eval->relinearize_inplace(vs[15], rk);
    
    // __t38 = blend(__v14@0000000000001000000000, __v2@0000000000000000001000)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(vs[14], bits["0000000000001000000000"], t38_1);
    info.eval->multiply_plain(vs[2], bits["0000000000000000001000"], t38_2);
    info.eval->add(t38_1, t38_2, ts[38]);
    
    
    // __t39 = blend(__v15@0000000000000000001000, __t37@0000000000001000000000)
    ctxt t39_1;
    info.eval->multiply_plain(vs[15], bits["0000000000000000001000"], t39_1);
    info.eval->add(t39_1, ts[37], ts[39]);
    
    info.eval->multiply(ts[38], ts[39], vs[16]); // __v16 = __t38 * __t39
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->rotate_rows(vs[16], -16, gk, ss[15]); // __s15 = __v16 >> 16
    info.eval->multiply(ss[15], vs[16], vs[17]); // __v17 = __s15 * __v16
    info.eval->relinearize_inplace(vs[17], rk);
    return vs[17];
}
    