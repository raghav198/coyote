
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000001", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "010000000", info);
    add_bitstring(bits, "000000100", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "001001000", info);
    add_bitstring(bits, "000010010", info);
    add_bitstring(bits, "000100000", info);
    add_bitstring(bits, "000010011", info);
    add_bitstring(bits, "011000000", info);
    add_bitstring(bits, "000000010", info);
    add_bitstring(bits, "000001100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(38);
    ts[0] = encrypt_input("10011100011100111", info);
    ts[1] = encrypt_input("110101100010100111", info);
    ts[2] = encrypt_input("111111011101100110", info);
    ts[3] = encrypt_input("101000101011100111", info);
    ts[4] = encrypt_input("10100011111111100", info);
    ts[5] = encrypt_input("1100011011111100", info);
    ts[8] = encrypt_input("0111000011110010", info);
    ts[9] = encrypt_input("011100001111110", info);
    ts[10] = encrypt_input("11111110101110000", info);
    ts[11] = encrypt_input("11011111101110000", info);
    ts[14] = encrypt_input("00011100111111111", info);
    ts[15] = encrypt_input("00011100111111101", info);
    ts[18] = encrypt_input("0000111001010", info);
    ts[19] = encrypt_input("0000111001110", info);
    ts[22] = encrypt_input("001110011111100", info);
    ts[23] = encrypt_input("001010010111000", info);
    ts[26] = encrypt_input("000011100111111", info);
    ts[27] = encrypt_input("000011000111101", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[16];
    ctxt ss[8];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t6 = blend(__v1@000000001, __t4@100011100)
    ctxt t6_1;
    info.eval->multiply_plain(vs[1], bits["000000001"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@000000001, __t5@100011100)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["000000001"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->add(ts[8], ts[9], vs[3]); // __v3 = __t8 + __t9
    
    // __t12 = blend(__v2@000001000, __t10@111010000)
    ctxt t12_1;
    info.eval->multiply_plain(vs[2], bits["000001000"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    
    // __t13 = blend(__v0@000001000, __t11@111010000)
    ctxt t13_1;
    info.eval->multiply_plain(vs[0], bits["000001000"], t13_1);
    info.eval->add(t13_1, ts[11], ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[4]); // __v4 = __t12 * __t13
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t16 = blend(__v1@100000000, __t14@000100111)
    ctxt t16_1;
    info.eval->multiply_plain(vs[1], bits["100000000"], t16_1);
    info.eval->add(t16_1, ts[14], ts[16]);
    
    
    // __t17 = blend(__v0@100000000, __t15@000100111)
    ctxt t17_1;
    info.eval->multiply_plain(vs[0], bits["100000000"], t17_1);
    info.eval->add(t17_1, ts[15], ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[5]); // __v5 = __t16 + __t17
    
    // __t20 = blend(__v2@100000000, __v4@010000000, __v5@000000100, __t18@000010010)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(vs[2], bits["100000000"], t20_1);
    info.eval->multiply_plain(vs[4], bits["010000000"], t20_2);
    info.eval->multiply_plain(vs[5], bits["000000100"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3, ts[18]}, ts[20]);
    
    
    // __t21 = blend(__v4@100000000, __v3@010000000, __v2@000000100, __t19@000010010)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(vs[4], bits["100000000"], t21_1);
    info.eval->multiply_plain(vs[3], bits["010000000"], t21_2);
    info.eval->multiply_plain(vs[2], bits["000000100"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3, ts[19]}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[6]); // __v6 = __t20 + __t21
    
    // __t24 = blend(__v0@010000000, __v1@000100000, __v4@000010000, __v5@000000010, __t22@001001100)
    ctxt t24_1, t24_2, t24_3, t24_4;
    info.eval->multiply_plain(vs[0], bits["010000000"], t24_1);
    info.eval->multiply_plain(vs[1], bits["000100000"], t24_2);
    info.eval->multiply_plain(vs[4], bits["000010000"], t24_3);
    info.eval->multiply_plain(vs[5], bits["000000010"], t24_4);
    info.eval->add_many({t24_1, t24_2, t24_3, t24_4, ts[22]}, ts[24]);
    
    
    // __t25 = blend(__v1@010000000, __v5@000100000, __v6@000010000, __v3@000000010, __t23@001001100)
    ctxt t25_1, t25_2, t25_3, t25_4;
    info.eval->multiply_plain(vs[1], bits["010000000"], t25_1);
    info.eval->multiply_plain(vs[5], bits["000100000"], t25_2);
    info.eval->multiply_plain(vs[6], bits["000010000"], t25_3);
    info.eval->multiply_plain(vs[3], bits["000000010"], t25_4);
    info.eval->add_many({t25_1, t25_2, t25_3, t25_4, ts[23]}, ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[7]); // __v7 = __t24 * __t25
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -7, gk, ss[0]); // __s0 = __v7 >> 7
    
    // __t28 = blend(__v5@100000000, __v1@000001000, __v3@000000100, __t26@000010011)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[5], bits["100000000"], t28_1);
    info.eval->multiply_plain(vs[1], bits["000001000"], t28_2);
    info.eval->multiply_plain(vs[3], bits["000000100"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3, ts[26]}, ts[28]);
    
    
    // __t29 = blend(__v6@100000000, __v7@000001100, __t27@000010011)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(vs[6], bits["100000000"], t29_1);
    info.eval->multiply_plain(vs[7], bits["000001100"], t29_2);
    info.eval->add_many({t29_1, t29_2, ts[27]}, ts[29]);
    
    info.eval->add(ts[28], ts[29], vs[8]); // __v8 = __t28 + __t29
    info.eval->rotate_rows(vs[8], -1, gk, ss[1]); // __s1 = __v8 >> 1
    
    // __t30 = blend(__v2@000010000, __v8@000000100, __v6@000000010, __v5@000000001)
    ctxt t30_1, t30_2, t30_3, t30_4;
    info.eval->multiply_plain(vs[2], bits["000010000"], t30_1);
    info.eval->multiply_plain(vs[8], bits["000000100"], t30_2);
    info.eval->multiply_plain(vs[6], bits["000000010"], t30_3);
    info.eval->multiply_plain(vs[5], bits["000000001"], t30_4);
    info.eval->add_many({t30_1, t30_2, t30_3, t30_4}, ts[30]);
    
    
    // __t31 = blend(__v8@000010011, __v6@000000100)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(vs[8], bits["000010011"], t31_1);
    info.eval->multiply_plain(vs[6], bits["000000100"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->add(ts[30], ts[31], vs[9]); // __v9 = __t30 + __t31
    
    // __t32 = blend(__v6@010000000, __v4@001001000, __v7@000010010, __v2@000000001)
    ctxt t32_1, t32_2, t32_3, t32_4;
    info.eval->multiply_plain(vs[6], bits["010000000"], t32_1);
    info.eval->multiply_plain(vs[4], bits["001001000"], t32_2);
    info.eval->multiply_plain(vs[7], bits["000010010"], t32_3);
    info.eval->multiply_plain(vs[2], bits["000000001"], t32_4);
    info.eval->add_many({t32_1, t32_2, t32_3, t32_4}, ts[32]);
    
    
    // __t33 = blend(__v7@011000000, __v9@000010011, __v8@000001000)
    ctxt t33_1, t33_2, t33_3;
    info.eval->multiply_plain(vs[7], bits["011000000"], t33_1);
    info.eval->multiply_plain(vs[9], bits["000010011"], t33_2);
    info.eval->multiply_plain(vs[8], bits["000001000"], t33_3);
    info.eval->add_many({t33_1, t33_2, t33_3}, ts[33]);
    
    info.eval->multiply(ts[32], ts[33], vs[10]); // __v10 = __t32 * __t33
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -8, gk, ss[2]); // __s2 = __v10 >> 8
    info.eval->rotate_rows(vs[10], -6, gk, ss[3]); // __s3 = __v10 >> 6
    info.eval->rotate_rows(vs[10], -1, gk, ss[4]); // __s4 = __v10 >> 1
    info.eval->rotate_rows(vs[10], -7, gk, ss[5]); // __s5 = __v10 >> 7
    
    // __t34 = blend(__s1@010000000, __v9@000000100)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(ss[1], bits["010000000"], t34_1);
    info.eval->multiply_plain(vs[9], bits["000000100"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    
    // __t35 = blend(__s3@010000000, __s4@000000100)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(ss[3], bits["010000000"], t35_1);
    info.eval->multiply_plain(ss[4], bits["000000100"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[11]); // __v11 = __t34 * __t35
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t36 = blend(__s0@010000000, __s5@000000100)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(ss[0], bits["010000000"], t36_1);
    info.eval->multiply_plain(ss[5], bits["000000100"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    info.eval->add(ss[2], ts[36], vs[12]); // __v12 = __s2 + __t36
    info.eval->multiply(vs[12], vs[10], vs[13]); // __v13 = __v12 * __v10
    info.eval->relinearize_inplace(vs[13], rk);
    
    // __t37 = blend(__v13@010000000, __v12@000000100)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(vs[13], bits["010000000"], t37_1);
    info.eval->multiply_plain(vs[12], bits["000000100"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    info.eval->add(ts[37], vs[11], vs[14]); // __v14 = __t37 + __v11
    info.eval->rotate_rows(vs[14], -8, gk, ss[6]); // __s6 = __v14 >> 8
    info.eval->rotate_rows(vs[14], -3, gk, ss[7]); // __s7 = __v14 >> 3
    info.eval->add(ss[6], ss[7], vs[15]); // __v15 = __s6 + __s7
    return vs[15];
}
    