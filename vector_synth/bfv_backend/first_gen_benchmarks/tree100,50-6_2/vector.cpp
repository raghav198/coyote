
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000001000000000000000000", info);
    add_bitstring(bits, "00000000000000100001000000", info);
    add_bitstring(bits, "00000000100000000000000000", info);
    add_bitstring(bits, "00000000000000000000001000", info);
    add_bitstring(bits, "01000010000000000000000000", info);
    add_bitstring(bits, "01010000000000000000000000", info);
    add_bitstring(bits, "00001000000000000000000010", info);
    add_bitstring(bits, "00000000000000000010000000", info);
    add_bitstring(bits, "00000000000001000000000000", info);
    add_bitstring(bits, "00000010000000000000000000", info);
    add_bitstring(bits, "01000000000000000000000000", info);
    add_bitstring(bits, "00000001000000000000100000", info);
    add_bitstring(bits, "00100000000000000000000000", info);
    add_bitstring(bits, "00000000000000000001000000", info);
    add_bitstring(bits, "10000000000000000000000000", info);
    add_bitstring(bits, "00000000000000001000000000", info);
    add_bitstring(bits, "00010000000000000000000000", info);
    add_bitstring(bits, "00000000000000100000000000", info);
    add_bitstring(bits, "00000000000000010000000000", info);
    add_bitstring(bits, "00000000000000000000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(28);
    ts[0] = encrypt_input("11110100111000111000001110111100000011100111", info);
    ts[1] = encrypt_input("1111101100001110000011101111110000011100111", info);
    ts[2] = encrypt_input("11100011100011100000011000000010101110", info);
    ts[3] = encrypt_input("111000111000110000000111000000101110", info);
    ts[4] = encrypt_input("0000111000001100111000011000111001110", info);
    ts[5] = encrypt_input("0000101000001110110000111000110001110", info);
    ts[8] = encrypt_input("01110001111110000001110011100011000000", info);
    ts[9] = encrypt_input("0111000111110000001110011100011100000", info);
    ts[12] = encrypt_input("0001110011001110000000000000000", info);
    ts[13] = encrypt_input("00010100111001110000000000000000", info);
    ts[16] = encrypt_input("00000000000000000011111000000", info);
    ts[17] = encrypt_input("000000000000000000101111000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[16];
    ctxt ss[20];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -21, gk, ss[1]); // __s1 = __v0 >> 21
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -24, gk, ss[2]); // __s2 = __v1 >> 24
    
    // __t6 = blend(__v1@10000000000000000000000000, __v0@00000000000000010000000000, __t4@00001000001010000100010010)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[1], bits["10000000000000000000000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00000000000000010000000000"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v0@10000000000000000000000000, __v1@00000000000000010000000000, __t5@00001000001010000100010010)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[0], bits["10000000000000000000000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["00000000000000010000000000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -1, gk, ss[3]); // __s3 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -24, gk, ss[4]); // __s4 = __v2 >> 24
    info.eval->rotate_rows(vs[2], -21, gk, ss[5]); // __s5 = __v2 >> 21
    
    // __t10 = blend(__v0@00000000000000000000001000, __t8@01000110000001001000100000)
    ctxt t10_1;
    info.eval->multiply_plain(vs[0], bits["00000000000000000000001000"], t10_1);
    info.eval->add(t10_1, ts[8], ts[10]);
    
    
    // __t11 = blend(__v1@00000000000000000000001000, __t9@01000110000001001000100000)
    ctxt t11_1;
    info.eval->multiply_plain(vs[1], bits["00000000000000000000001000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[3]); // __v3 = __t10 + __t11
    info.eval->rotate_rows(vs[3], -1, gk, ss[6]); // __s6 = __v3 >> 1
    info.eval->rotate_rows(vs[3], -24, gk, ss[7]); // __s7 = __v3 >> 24
    
    // __t14 = blend(__v1@00001000000000000000000010, __v3@00000000000000001000000000, __t12@00010010010000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[1], bits["00001000000000000000000010"], t14_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000001000000000"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[12]}, ts[14]);
    
    
    // __t15 = blend(__v2@00001000000000000000000010, __v0@00000000000000001000000000, __t13@00010010010000000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[2], bits["00001000000000000000000010"], t15_1);
    info.eval->multiply_plain(vs[0], bits["00000000000000001000000000"], t15_2);
    info.eval->add_many({t15_1, t15_2, ts[13]}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[4]); // __v4 = __t14 * __t15
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -24, gk, ss[8]); // __s8 = __v4 >> 24
    info.eval->rotate_rows(vs[4], -21, gk, ss[9]); // __s9 = __v4 >> 21
    
    // __t18 = blend(__v0@01010000000000000000000000, __v4@00000010000000000000000000, __v3@00000000000001000000000000, __t16@00000000000000000011000000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[0], bits["01010000000000000000000000"], t18_1);
    info.eval->multiply_plain(vs[4], bits["00000010000000000000000000"], t18_2);
    info.eval->multiply_plain(vs[3], bits["00000000000001000000000000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3, ts[16]}, ts[18]);
    
    
    // __t19 = blend(__v3@01000010000000000000000000, __v4@00010000000000000000000000, __v0@00000000000001000000000000, __t17@00000000000000000011000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[3], bits["01000010000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[4], bits["00010000000000000000000000"], t19_2);
    info.eval->multiply_plain(vs[0], bits["00000000000001000000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3, ts[17]}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[5]); // __v5 = __t18 + __t19
    info.eval->rotate_rows(vs[5], -1, gk, ss[10]); // __s10 = __v5 >> 1
    info.eval->rotate_rows(vs[5], -24, gk, ss[11]); // __s11 = __v5 >> 24
    
    // __t20 = blend(__s5@00000001000000000000000000, __s8@00000000000000100000000000, __s7@00000000000000000010000000, __s4@00000000000000000001000000, __s10@00000000000000000000100000)
    ctxt t20_1, t20_2, t20_3, t20_4, t20_5;
    info.eval->multiply_plain(ss[5], bits["00000001000000000000000000"], t20_1);
    info.eval->multiply_plain(ss[8], bits["00000000000000100000000000"], t20_2);
    info.eval->multiply_plain(ss[7], bits["00000000000000000010000000"], t20_3);
    info.eval->multiply_plain(ss[4], bits["00000000000000000001000000"], t20_4);
    info.eval->multiply_plain(ss[10], bits["00000000000000000000100000"], t20_5);
    info.eval->add_many({t20_1, t20_2, t20_3, t20_4, t20_5}, ts[20]);
    
    
    // __t21 = blend(__s8@00000001000000000000000000, __s10@00000000000000100001000000, __s3@00000000000000000010000000, __s1@00000000000000000000100000)
    ctxt t21_1, t21_2, t21_3, t21_4;
    info.eval->multiply_plain(ss[8], bits["00000001000000000000000000"], t21_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000100001000000"], t21_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000000010000000"], t21_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000100000"], t21_4);
    info.eval->add_many({t21_1, t21_2, t21_3, t21_4}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[6]); // __v6 = __t20 + __t21
    info.eval->rotate_rows(vs[6], -13, gk, ss[12]); // __s12 = __v6 >> 13
    info.eval->rotate_rows(vs[6], -21, gk, ss[13]); // __s13 = __v6 >> 21
    
    // __t22 = blend(__s8@00100000000000000000000000, __s2@00000010000000000000000000, __s10@00000001000000000000000000, __s4@00000000100000000000000000, __v6@00000000000000000001000000, __s7@00000000000000000000100000)
    ctxt t22_1, t22_2, t22_3, t22_4, t22_5, t22_6;
    info.eval->multiply_plain(ss[8], bits["00100000000000000000000000"], t22_1);
    info.eval->multiply_plain(ss[2], bits["00000010000000000000000000"], t22_2);
    info.eval->multiply_plain(ss[10], bits["00000001000000000000000000"], t22_3);
    info.eval->multiply_plain(ss[4], bits["00000000100000000000000000"], t22_4);
    info.eval->multiply_plain(vs[6], bits["00000000000000000001000000"], t22_5);
    info.eval->multiply_plain(ss[7], bits["00000000000000000000100000"], t22_6);
    info.eval->add_many({t22_1, t22_2, t22_3, t22_4, t22_5, t22_6}, ts[22]);
    
    
    // __t23 = blend(__s10@00100000000000000000000000, __s6@00000010000000000000000000, __v6@00000001000000000000100000, __s0@00000000100000000000000000, __s9@00000000000000000001000000)
    ctxt t23_1, t23_2, t23_3, t23_4, t23_5;
    info.eval->multiply_plain(ss[10], bits["00100000000000000000000000"], t23_1);
    info.eval->multiply_plain(ss[6], bits["00000010000000000000000000"], t23_2);
    info.eval->multiply_plain(vs[6], bits["00000001000000000000100000"], t23_3);
    info.eval->multiply_plain(ss[0], bits["00000000100000000000000000"], t23_4);
    info.eval->multiply_plain(ss[9], bits["00000000000000000001000000"], t23_5);
    info.eval->add_many({t23_1, t23_2, t23_3, t23_4, t23_5}, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[7]); // __v7 = __t22 * __t23
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -24, gk, ss[14]); // __s14 = __v7 >> 24
    info.eval->rotate_rows(vs[7], -21, gk, ss[15]); // __s15 = __v7 >> 21
    info.eval->rotate_rows(vs[7], -19, gk, ss[16]); // __s16 = __v7 >> 19
    info.eval->rotate_rows(vs[7], -8, gk, ss[17]); // __s17 = __v7 >> 8
    
    // __t24 = blend(__s15@01000000000000000000000000, __s13@00000000000001000000000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(ss[15], bits["01000000000000000000000000"], t24_1);
    info.eval->multiply_plain(ss[13], bits["00000000000001000000000000"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    
    // __t25 = blend(__s11@01000000000000000000000000, __s4@00000000000001000000000000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(ss[11], bits["01000000000000000000000000"], t25_1);
    info.eval->multiply_plain(ss[4], bits["00000000000001000000000000"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    info.eval->add(ts[24], ts[25], vs[8]); // __v8 = __t24 + __t25
    info.eval->add(ss[16], ss[3], vs[9]); // __v9 = __s16 + __s3
    info.eval->add(vs[8], vs[9], vs[10]); // __v10 = __v8 + __v9
    info.eval->add(ss[12], ss[17], vs[11]); // __v11 = __s12 + __s17
    
    // __t26 = blend(__v10@01000000000000000000000000, __v8@00000000000001000000000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(vs[10], bits["01000000000000000000000000"], t26_1);
    info.eval->multiply_plain(vs[8], bits["00000000000001000000000000"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__v11@01000000000000000000000000, __s16@00000000000001000000000000)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(vs[11], bits["01000000000000000000000000"], t27_1);
    info.eval->multiply_plain(ss[16], bits["00000000000001000000000000"], t27_2);
    info.eval->add(t27_1, t27_2, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[12]); // __v12 = __t26 * __t27
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -25, gk, ss[18]); // __s18 = __v12 >> 25
    info.eval->rotate_rows(vs[12], -13, gk, ss[19]); // __s19 = __v12 >> 13
    info.eval->add(ss[14], ss[16], vs[13]); // __v13 = __s14 + __s16
    info.eval->add(ss[19], vs[13], vs[14]); // __v14 = __s19 + __v13
    info.eval->add(vs[14], ss[18], vs[15]); // __v15 = __v14 + __s18
    return vs[15];
}
    