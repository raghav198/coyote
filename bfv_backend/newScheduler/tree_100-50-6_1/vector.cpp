
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000010000000000000000", info);
    add_bitstring(bits, "00000100000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000010000000", info);
    add_bitstring(bits, "00000000001000000000000000000000", info);
    add_bitstring(bits, "00000001000000000000000001000000", info);
    add_bitstring(bits, "00000000000000000000011000000000", info);
    add_bitstring(bits, "00010000100000010000000000000010", info);
    add_bitstring(bits, "00000000001000000000010000000000", info);
    add_bitstring(bits, "00000000000001000000000001000000", info);
    add_bitstring(bits, "00000000000000000000010000000000", info);
    add_bitstring(bits, "00000000000000000000000000001000", info);
    add_bitstring(bits, "00000001000000000000000000000000", info);
    add_bitstring(bits, "00010000000000000000000000000010", info);
    add_bitstring(bits, "00000000000000000010000000000000", info);
    add_bitstring(bits, "00000000100000000000000010000000", info);
    add_bitstring(bits, "01000000000000000000000000000000", info);
    add_bitstring(bits, "00000000100000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000001000000000", info);
    add_bitstring(bits, "00000000000001000000000000001000", info);
    add_bitstring(bits, "00000100000000000000010000000000", info);
    add_bitstring(bits, "00000000000000000000000001000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(22);
    ts[0] = encrypt_input("00011101110111111111011101111110110001100001110000111111", info);
    ts[1] = encrypt_input("0001110110011110111101110111111111011000101000011100001011111", info);
    ts[2] = encrypt_input("1100110011101110001010000000111001111111111000111011100", info);
    ts[3] = encrypt_input("110101011101110001010000000011100110111111110011011000", info);
    ts[4] = encrypt_input("0000011100000000000000001011000000000", info);
    ts[5] = encrypt_input("000001110000000000000000111000000000", info);
    ts[8] = encrypt_input("00000000111000000000000000111000111000", info);
    ts[9] = encrypt_input("0000000011000000000000000111000111000", info);
    ts[14] = encrypt_input("0000000000000000000000001110000000", info);
    ts[15] = encrypt_input("0000000000000000000000001110000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[15];
    ctxt ss[13];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -29, gk, ss[1]); // __s1 = __v0 >> 29
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -29, gk, ss[3]); // __s3 = __v1 >> 29
    
    // __t6 = blend(__s3@00000001000000000000000000000000, __v1@00000000000000000010000000000000, __v0@00000000000000000000000001000000, __t4@00000100000000000000001000000000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[3], bits["00000001000000000000000000000000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["00000000000000000010000000000000"], t6_2);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000000001000000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__s2@00000001000000000000000001000000, __s0@00000000000000000010000000000000, __t5@00000100000000000000001000000000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[2], bits["00000001000000000000000001000000"], t7_1);
    info.eval->multiply_plain(ss[0], bits["00000000000000000010000000000000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -30, gk, ss[4]); // __s4 = __v2 >> 30
    info.eval->rotate_rows(vs[2], -3, gk, ss[5]); // __s5 = __v2 >> 3
    
    // __t10 = blend(__s2@01000000000000000000000000000000, __v2@00000100000000000000000000000000, __s1@00000000001000000000000000000000, __v1@00000000000000000000011000000000, __t8@00000000100000000000000010001000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[2], bits["01000000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["00000100000000000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[1], bits["00000000001000000000000000000000"], t10_3);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000011000000000"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__s3@01000000000000000000000000000000, __v0@00000100000000000000000000000000, __s0@00000000001000000000010000000000, __v2@00000000000000000000001000000000, __t9@00000000100000000000000010001000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[3], bits["01000000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[0], bits["00000100000000000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[0], bits["00000000001000000000010000000000"], t11_3);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000001000000000"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -3, gk, ss[6]); // __s6 = __v3 >> 3
    
    // __t12 = blend(__s2@00010000000000000000000000000010, __v3@00000000100000000000000010000000, __s0@00000000000000010000000000000000, __s1@00000000000000000000000000001000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[2], bits["00010000000000000000000000000010"], t12_1);
    info.eval->multiply_plain(vs[3], bits["00000000100000000000000010000000"], t12_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000010000000000000000"], t12_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000000000001000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__v0@00010000100000010000000000000010, __s2@00000000000000000000000010000000, __v3@00000000000000000000000000001000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[0], bits["00010000100000010000000000000010"], t13_1);
    info.eval->multiply_plain(ss[2], bits["00000000000000000000000010000000"], t13_2);
    info.eval->multiply_plain(vs[3], bits["00000000000000000000000000001000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[4]); // __v4 = __t12 + __t13
    info.eval->rotate_rows(vs[4], -30, gk, ss[7]); // __s7 = __v4 >> 30
    info.eval->add(ts[14], ts[15], vs[5]); // __v5 = __t14 + __t15
    
    // __t16 = blend(__s4@00000100000000000000000000000000, __s7@00000000000001000000000000001000, __s5@00000000000000000000010000000000, __s3@00000000000000000000000010000000, __v2@00000000000000000000000001000000)
    ctxt t16_1, t16_2, t16_3, t16_4, t16_5;
    info.eval->multiply_plain(ss[4], bits["00000100000000000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[7], bits["00000000000001000000000000001000"], t16_2);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000010000000000"], t16_3);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000000010000000"], t16_4);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000000001000000"], t16_5);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, t16_5}, ts[16]);
    
    
    // __t17 = blend(__v3@00000100000000000000010000000000, __s6@00000000000001000000000001000000, __v5@00000000000000000000000010000000, __v4@00000000000000000000000000001000)
    ctxt t17_1, t17_2, t17_3, t17_4;
    info.eval->multiply_plain(vs[3], bits["00000100000000000000010000000000"], t17_1);
    info.eval->multiply_plain(ss[6], bits["00000000000001000000000001000000"], t17_2);
    info.eval->multiply_plain(vs[5], bits["00000000000000000000000010000000"], t17_3);
    info.eval->multiply_plain(vs[4], bits["00000000000000000000000000001000"], t17_4);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4}, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[6]); // __v6 = __t16 * __t17
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -20, gk, ss[8]); // __s8 = __v6 >> 20
    info.eval->rotate_rows(vs[6], -12, gk, ss[9]); // __s9 = __v6 >> 12
    info.eval->add(vs[6], vs[4], vs[7]); // __v7 = __v6 + __v4
    info.eval->rotate_rows(vs[7], -9, gk, ss[10]); // __s10 = __v7 >> 9
    info.eval->add(ss[1], ss[0], vs[8]); // __v8 = __s1 + __s0
    info.eval->multiply(ss[7], vs[3], vs[9]); // __v9 = __s7 * __v3
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t18 = blend(__s8@01000000000000000000000000000000, __s9@00000100000000000000000000000000, __v4@00000000100000000000000000000000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(ss[8], bits["01000000000000000000000000000000"], t18_1);
    info.eval->multiply_plain(ss[9], bits["00000100000000000000000000000000"], t18_2);
    info.eval->multiply_plain(vs[4], bits["00000000100000000000000000000000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    
    // __t19 = blend(__v9@01000000000000000000000000000000, __v6@00000100000000000000000000000000, __v8@00000000100000000000000000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[9], bits["01000000000000000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[6], bits["00000100000000000000000000000000"], t19_2);
    info.eval->multiply_plain(vs[8], bits["00000000100000000000000000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[10]); // __v10 = __t18 + __t19
    info.eval->rotate_rows(vs[10], -28, gk, ss[11]); // __s11 = __v10 >> 28
    
    // __t20 = blend(__s10@01000000000000000000000000000000, __s9@00000000100000000000000000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(ss[10], bits["01000000000000000000000000000000"], t20_1);
    info.eval->multiply_plain(ss[9], bits["00000000100000000000000000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__s9@01000000000000000000000000000000, __v10@00000000100000000000000000000000)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(ss[9], bits["01000000000000000000000000000000"], t21_1);
    info.eval->multiply_plain(vs[10], bits["00000000100000000000000000000000"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->multiply(ts[20], ts[21], vs[11]); // __v11 = __t20 * __t21
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -25, gk, ss[12]); // __s12 = __v11 >> 25
    info.eval->multiply(ss[12], vs[11], vs[12]); // __v12 = __s12 * __v11
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->add(vs[10], ss[11], vs[13]); // __v13 = __v10 + __s11
    info.eval->multiply(vs[12], vs[13], vs[14]); // __v14 = __v12 * __v13
    info.eval->relinearize_inplace(vs[14], rk);
    return vs[14];
}
    