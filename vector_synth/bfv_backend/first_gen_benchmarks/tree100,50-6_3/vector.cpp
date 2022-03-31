
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000010000000000", info);
    add_bitstring(bits, "00000000101000000", info);
    add_bitstring(bits, "00100000101000000", info);
    add_bitstring(bits, "00000000000000100", info);
    add_bitstring(bits, "00010000001000000", info);
    add_bitstring(bits, "10000000000000000", info);
    add_bitstring(bits, "00000000000000110", info);
    add_bitstring(bits, "00100000000000000", info);
    add_bitstring(bits, "00000100000000000", info);
    add_bitstring(bits, "00000001000000000", info);
    add_bitstring(bits, "00000000001000010", info);
    add_bitstring(bits, "00000000001010000", info);
    add_bitstring(bits, "00000000000000010", info);
    add_bitstring(bits, "00000000000010000", info);
    add_bitstring(bits, "00010000000000000", info);
    add_bitstring(bits, "00000000001000000", info);
    add_bitstring(bits, "00001000000000000", info);
    add_bitstring(bits, "00000000000001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(34);
    ts[0] = encrypt_input("1101010011101111111100111000000", info);
    ts[1] = encrypt_input("111111001110101111111011000000", info);
    ts[2] = encrypt_input("0010101110011100111000000", info);
    ts[3] = encrypt_input("001101110011100111000000", info);
    ts[4] = encrypt_input("0011111111110111101110110111001011110", info);
    ts[5] = encrypt_input("0011111111111111001110101111001011100", info);
    ts[8] = encrypt_input("000000000000101111110100", info);
    ts[9] = encrypt_input("0000000000001111111110110", info);
    ts[12] = encrypt_input("000011100001111010111001100", info);
    ts[13] = encrypt_input("0000111000011111011001110", info);
    ts[16] = encrypt_input("0001110000000000000", info);
    ts[17] = encrypt_input("0001110000000000000", info);
    ts[22] = encrypt_input("100000000000000000", info);
    ts[23] = encrypt_input("1110000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[18];
    ctxt ss[14];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    
    // __t6 = blend(__v0@00000001000000000, __t4@00111110101100110)
    ctxt t6_1;
    info.eval->multiply_plain(vs[0], bits["00000001000000000"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v1@00000001000000000, __t5@00111110101100110)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["00000001000000000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -4, gk, ss[1]); // __s1 = __v2 >> 4
    
    // __t10 = blend(__v1@00100000000000000, __v2@00001000000000000, __v0@00000000101000000, __t8@00000000000011101)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[1], bits["00100000000000000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["00001000000000000"], t10_2);
    info.eval->multiply_plain(vs[0], bits["00000000101000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__v2@00100000101000000, __v1@00001000000000000, __t9@00000000000011101)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[2], bits["00100000101000000"], t11_1);
    info.eval->multiply_plain(vs[1], bits["00001000000000000"], t11_2);
    info.eval->add_many({t11_1, t11_2, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -4, gk, ss[2]); // __s2 = __v3 >> 4
    info.eval->rotate_rows(vs[3], -16, gk, ss[3]); // __s3 = __v3 >> 16
    
    // __t14 = blend(__v0@00000010000000000, __t12@00001000011010010)
    ctxt t14_1;
    info.eval->multiply_plain(vs[0], bits["00000010000000000"], t14_1);
    info.eval->add(t14_1, ts[12], ts[14]);
    
    
    // __t15 = blend(__v2@00000010000000000, __t13@00001000011010010)
    ctxt t15_1;
    info.eval->multiply_plain(vs[2], bits["00000010000000000"], t15_1);
    info.eval->add(t15_1, ts[13], ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[4]); // __v4 = __t14 + __t15
    info.eval->rotate_rows(vs[4], -4, gk, ss[4]); // __s4 = __v4 >> 4
    
    // __t18 = blend(__v0@00001000000000000, __v4@00000000001000010, __v3@00000000000000100, __t16@00010000000000000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[0], bits["00001000000000000"], t18_1);
    info.eval->multiply_plain(vs[4], bits["00000000001000010"], t18_2);
    info.eval->multiply_plain(vs[3], bits["00000000000000100"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3, ts[16]}, ts[18]);
    
    
    // __t19 = blend(__v4@00001000000000000, __v1@00000000001000000, __v2@00000000000000110, __t17@00010000000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[4], bits["00001000000000000"], t19_1);
    info.eval->multiply_plain(vs[1], bits["00000000001000000"], t19_2);
    info.eval->multiply_plain(vs[2], bits["00000000000000110"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3, ts[17]}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[5]); // __v5 = __t18 + __t19
    info.eval->rotate_rows(vs[5], -16, gk, ss[5]); // __s5 = __v5 >> 16
    
    // __t20 = blend(__v2@00010000000000000, __v5@00001000000000000, __v3@00000000001010000)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(vs[2], bits["00010000000000000"], t20_1);
    info.eval->multiply_plain(vs[5], bits["00001000000000000"], t20_2);
    info.eval->multiply_plain(vs[3], bits["00000000001010000"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3}, ts[20]);
    
    
    // __t21 = blend(__v5@00010000001000000, __v3@00001000000000000, __v4@00000000000010000)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(vs[5], bits["00010000001000000"], t21_1);
    info.eval->multiply_plain(vs[3], bits["00001000000000000"], t21_2);
    info.eval->multiply_plain(vs[4], bits["00000000000010000"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[6]); // __v6 = __t20 + __t21
    info.eval->rotate_rows(vs[6], -4, gk, ss[6]); // __s6 = __v6 >> 4
    
    // __t24 = blend(__v2@00000100000000000, __v3@00000000000001000, __t22@10000000000000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[2], bits["00000100000000000"], t24_1);
    info.eval->multiply_plain(vs[3], bits["00000000000001000"], t24_2);
    info.eval->add_many({t24_1, t24_2, ts[22]}, ts[24]);
    
    
    // __t25 = blend(__s0@00000100000000000, __s4@00000000000001000, __t23@10000000000000000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(ss[0], bits["00000100000000000"], t25_1);
    info.eval->multiply_plain(ss[4], bits["00000000000001000"], t25_2);
    info.eval->add_many({t25_1, t25_2, ts[23]}, ts[25]);
    
    info.eval->add(ts[24], ts[25], vs[7]); // __v7 = __t24 + __t25
    info.eval->rotate_rows(vs[7], -16, gk, ss[7]); // __s7 = __v7 >> 16
    
    // __t26 = blend(__v2@00000001000000000, __v7@00000000000001000, __s1@00000000000000010)
    ctxt t26_1, t26_2, t26_3;
    info.eval->multiply_plain(vs[2], bits["00000001000000000"], t26_1);
    info.eval->multiply_plain(vs[7], bits["00000000000001000"], t26_2);
    info.eval->multiply_plain(ss[1], bits["00000000000000010"], t26_3);
    info.eval->add_many({t26_1, t26_2, t26_3}, ts[26]);
    
    
    // __t27 = blend(__s6@00000001000000000, __s5@00000000000001000, __s3@00000000000000010)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(ss[6], bits["00000001000000000"], t27_1);
    info.eval->multiply_plain(ss[5], bits["00000000000001000"], t27_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000010"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3}, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[8]); // __v8 = __t26 * __t27
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -14, gk, ss[8]); // __s8 = __v8 >> 14
    
    // __t28 = blend(__v7@10000000000000000, __v6@00000000000010000)
    ctxt t28_1, t28_2;
    info.eval->multiply_plain(vs[7], bits["10000000000000000"], t28_1);
    info.eval->multiply_plain(vs[6], bits["00000000000010000"], t28_2);
    info.eval->add(t28_1, t28_2, ts[28]);
    
    
    // __t29 = blend(__v0@10000000000000000, __s2@00000000000010000)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(vs[0], bits["10000000000000000"], t29_1);
    info.eval->multiply_plain(ss[2], bits["00000000000010000"], t29_2);
    info.eval->add(t29_1, t29_2, ts[29]);
    
    info.eval->add(ts[28], ts[29], vs[9]); // __v9 = __t28 + __t29
    info.eval->rotate_rows(vs[9], -4, gk, ss[9]); // __s9 = __v9 >> 4
    
    // __t30 = blend(__v4@00000010000000000, __v5@00000000000000010)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(vs[4], bits["00000010000000000"], t30_1);
    info.eval->multiply_plain(vs[5], bits["00000000000000010"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    
    // __t31 = blend(__s2@00000010000000000, __v8@00000000000000010)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(ss[2], bits["00000010000000000"], t31_1);
    info.eval->multiply_plain(vs[8], bits["00000000000000010"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[10]); // __v10 = __t30 * __t31
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -15, gk, ss[10]); // __s10 = __v10 >> 15
    info.eval->rotate_rows(vs[10], -14, gk, ss[11]); // __s11 = __v10 >> 14
    info.eval->add(ss[8], ss[10], vs[11]); // __v11 = __s8 + __s10
    info.eval->add(ss[7], ss[9], vs[12]); // __v12 = __s7 + __s9
    info.eval->add(vs[6], vs[12], vs[13]); // __v13 = __v6 + __v12
    
    // __t32 = blend(__v13@00001000000000000, __s11@00000000000010000)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(vs[13], bits["00001000000000000"], t32_1);
    info.eval->multiply_plain(ss[11], bits["00000000000010000"], t32_2);
    info.eval->add(t32_1, t32_2, ts[32]);
    
    
    // __t33 = blend(__v11@00001000000000000, __v9@00000000000010000)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(vs[11], bits["00001000000000000"], t33_1);
    info.eval->multiply_plain(vs[9], bits["00000000000010000"], t33_2);
    info.eval->add(t33_1, t33_2, ts[33]);
    
    info.eval->multiply(ts[32], ts[33], vs[14]); // __v14 = __t32 * __t33
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -6, gk, ss[12]); // __s12 = __v14 >> 6
    info.eval->rotate_rows(vs[14], -15, gk, ss[13]); // __s13 = __v14 >> 15
    info.eval->add(ss[8], vs[6], vs[15]); // __v15 = __s8 + __v6
    info.eval->add(vs[15], ss[13], vs[16]); // __v16 = __v15 + __s13
    info.eval->multiply(vs[16], ss[12], vs[17]); // __v17 = __v16 * __s12
    info.eval->relinearize_inplace(vs[17], rk);
    return vs[17];
}
    