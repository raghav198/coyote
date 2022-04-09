
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00100000010000000000", info);
    add_bitstring(bits, "00000100000000000000", info);
    add_bitstring(bits, "00000000000000001000", info);
    add_bitstring(bits, "00000000000000010000", info);
    add_bitstring(bits, "00000100000000000010", info);
    add_bitstring(bits, "00000000000010000010", info);
    add_bitstring(bits, "00000000000001000000", info);
    add_bitstring(bits, "10000000000000000000", info);
    add_bitstring(bits, "00000000000000100000", info);
    add_bitstring(bits, "01000000000000000000", info);
    add_bitstring(bits, "00000010000000000000", info);
    add_bitstring(bits, "00000000000000000001", info);
    add_bitstring(bits, "00000000000010000000", info);
    add_bitstring(bits, "00000000000000000010", info);
    add_bitstring(bits, "00000000010000000000", info);
    add_bitstring(bits, "00000000000010100000", info);
    add_bitstring(bits, "00100000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(38);
    ts[0] = encrypt_input("11101110001011110111111110011100110000", info);
    ts[1] = encrypt_input("1110110001111110111111111011100110000", info);
    ts[2] = encrypt_input("1111110011100000001100111110110111111", info);
    ts[3] = encrypt_input("1111100111000000011001111110110111111", info);
    ts[4] = encrypt_input("000000000000001110001110", info);
    ts[5] = encrypt_input("000000000000001110001110", info);
    ts[8] = encrypt_input("00110000000000011100000", info);
    ts[9] = encrypt_input("001110000000000011100000", info);
    ts[10] = encrypt_input("000000000000111000111000", info);
    ts[11] = encrypt_input("0000000000001011000111000", info);
    ts[16] = encrypt_input("0000001110000011111100001110", info);
    ts[17] = encrypt_input("00000011100000101111100001100", info);
    ts[18] = encrypt_input("0000000000001110000000", info);
    ts[19] = encrypt_input("000000000000110000000", info);
    ts[22] = encrypt_input("0000000000000111000000", info);
    ts[23] = encrypt_input("0000000000000111000000", info);
    ts[30] = encrypt_input("00000000000000000010010", info);
    ts[31] = encrypt_input("0000000000000000001110", info);
    ts[32] = encrypt_input("0000000000000000001010", info);
    ts[33] = encrypt_input("0000000000000000001110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[23];
    ctxt ss[13];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -15, gk, ss[0]); // __s0 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -5, gk, ss[1]); // __s1 = __v0 >> 5
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->rotate_rows(vs[1], -5, gk, ss[2]); // __s2 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -15, gk, ss[3]); // __s3 = __v1 >> 15
    
    // __t6 = blend(__v0@10000000000000000000, __t4@00000000000000100010)
    ctxt t6_1;
    info.eval->multiply_plain(vs[0], bits["10000000000000000000"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v1@10000000000000000000, __t5@00000000000000100010)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["10000000000000000000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -5, gk, ss[4]); // __s4 = __v2 >> 5
    info.eval->add(vs[1], vs[2], vs[3]); // __v3 = __v1 + __v2
    info.eval->rotate_rows(vs[3], -5, gk, ss[5]); // __s5 = __v3 >> 5
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t12 = blend(__s0@01000000000000000000, __s3@00000000000010100000, __v0@00000000000000001000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[0], bits["01000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[3], bits["00000000000010100000"], t12_2);
    info.eval->multiply_plain(vs[0], bits["00000000000000001000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__v1@01000000000000000000, __s1@00000000000010000000, __v4@00000000000000100000, __v5@00000000000000001000)
    ctxt t13_1, t13_2, t13_3, t13_4;
    info.eval->multiply_plain(vs[1], bits["01000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[1], bits["00000000000010000000"], t13_2);
    info.eval->multiply_plain(vs[4], bits["00000000000000100000"], t13_3);
    info.eval->multiply_plain(vs[5], bits["00000000000000001000"], t13_4);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    info.eval->rotate_rows(vs[6], -4, gk, ss[6]); // __s6 = __v6 >> 4
    
    // __t14 = blend(__v0@00100000010000000000, __v5@00000000000010000000, __v1@00000000000000010000)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(vs[0], bits["00100000010000000000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["00000000000010000000"], t14_2);
    info.eval->multiply_plain(vs[1], bits["00000000000000010000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3}, ts[14]);
    
    
    // __t15 = blend(__v4@00100000000000000000, __s2@00000000010000000000, __v1@00000000000010000000, __s1@00000000000000010000)
    ctxt t15_1, t15_2, t15_3, t15_4;
    info.eval->multiply_plain(vs[4], bits["00100000000000000000"], t15_1);
    info.eval->multiply_plain(ss[2], bits["00000000010000000000"], t15_2);
    info.eval->multiply_plain(vs[1], bits["00000000000010000000"], t15_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000010000"], t15_4);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -4, gk, ss[7]); // __s7 = __v7 >> 4
    info.eval->multiply(ts[16], ts[17], vs[8]); // __v8 = __t16 * __t17
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t20 = blend(__v8@00000010000000000000, __v6@00000000000000001000, __t18@00000000000010000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[8], bits["00000010000000000000"], t20_1);
    info.eval->multiply_plain(vs[6], bits["00000000000000001000"], t20_2);
    info.eval->add_many({t20_1, t20_2, ts[18]}, ts[20]);
    
    
    // __t21 = blend(__s0@00000010000000000000, __s7@00000000000000001000, __t19@00000000000010000000)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(ss[0], bits["00000010000000000000"], t21_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000001000"], t21_2);
    info.eval->add_many({t21_1, t21_2, ts[19]}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[9]); // __v9 = __t20 + __t21
    info.eval->rotate_rows(vs[9], -3, gk, ss[8]); // __s8 = __v9 >> 3
    
    // __t24 = blend(__v9@00000000000010000000, __s1@00000000000000000010, __t22@00000000000001000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[9], bits["00000000000010000000"], t24_1);
    info.eval->multiply_plain(ss[1], bits["00000000000000000010"], t24_2);
    info.eval->add_many({t24_1, t24_2, ts[22]}, ts[24]);
    
    
    // __t25 = blend(__v8@00000000000010000010, __t23@00000000000001000000)
    ctxt t25_1;
    info.eval->multiply_plain(vs[8], bits["00000000000010000010"], t25_1);
    info.eval->add(t25_1, ts[23], ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[10]); // __v10 = __t24 * __t25
    info.eval->relinearize_inplace(vs[10], rk);
    
    // __t26 = blend(__s7@00000010000000000000, __v8@00000000000001000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(ss[7], bits["00000010000000000000"], t26_1);
    info.eval->multiply_plain(vs[8], bits["00000000000001000000"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__v9@00000010000000000000, __v10@00000000000001000000)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(vs[9], bits["00000010000000000000"], t27_1);
    info.eval->multiply_plain(vs[10], bits["00000000000001000000"], t27_2);
    info.eval->add(t27_1, t27_2, ts[27]);
    
    info.eval->add(ts[26], ts[27], vs[11]); // __v11 = __t26 + __t27
    info.eval->rotate_rows(vs[11], -13, gk, ss[9]); // __s9 = __v11 >> 13
    
    // __t28 = blend(__s4@00000100000000000000, __v6@00000000000010000000, __v11@00000000000001000000, __v10@00000000000000000010)
    ctxt t28_1, t28_2, t28_3, t28_4;
    info.eval->multiply_plain(ss[4], bits["00000100000000000000"], t28_1);
    info.eval->multiply_plain(vs[6], bits["00000000000010000000"], t28_2);
    info.eval->multiply_plain(vs[11], bits["00000000000001000000"], t28_3);
    info.eval->multiply_plain(vs[10], bits["00000000000000000010"], t28_4);
    info.eval->add_many({t28_1, t28_2, t28_3, t28_4}, ts[28]);
    
    
    // __t29 = blend(__s6@00000100000000000010, __v10@00000000000010000000, __s7@00000000000001000000)
    ctxt t29_1, t29_2, t29_3;
    info.eval->multiply_plain(ss[6], bits["00000100000000000010"], t29_1);
    info.eval->multiply_plain(vs[10], bits["00000000000010000000"], t29_2);
    info.eval->multiply_plain(ss[7], bits["00000000000001000000"], t29_3);
    info.eval->add_many({t29_1, t29_2, t29_3}, ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[12]); // __v12 = __t28 * __t29
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -13, gk, ss[10]); // __s10 = __v12 >> 13
    info.eval->rotate_rows(vs[12], -6, gk, ss[11]); // __s11 = __v12 >> 6
    info.eval->add(ts[30], ts[31], vs[13]); // __v13 = __t30 + __t31
    info.eval->add(ts[32], ts[33], vs[14]); // __v14 = __t32 + __t33
    
    // __t34 = blend(__s10@00000000000000000010, __s5@00000000000000000001)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(ss[10], bits["00000000000000000010"], t34_1);
    info.eval->multiply_plain(ss[5], bits["00000000000000000001"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    
    // __t35 = blend(__s11@00000000000000000010, __s7@00000000000000000001)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(ss[11], bits["00000000000000000010"], t35_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000000001"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[15]); // __v15 = __t34 * __t35
    info.eval->relinearize_inplace(vs[15], rk);
    
    // __t36 = blend(__v14@00000000000000000010, __s8@00000000000000000001)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(vs[14], bits["00000000000000000010"], t36_1);
    info.eval->multiply_plain(ss[8], bits["00000000000000000001"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    
    // __t37 = blend(__v13@00000000000000000010, __v15@00000000000000000001)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(vs[13], bits["00000000000000000010"], t37_1);
    info.eval->multiply_plain(vs[15], bits["00000000000000000001"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    info.eval->add(ts[36], ts[37], vs[16]); // __v16 = __t36 + __t37
    info.eval->multiply(vs[3], vs[16], vs[17]); // __v17 = __v3 * __v16
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->add(vs[17], vs[12], vs[18]); // __v18 = __v17 + __v12
    info.eval->multiply(vs[18], vs[15], vs[19]); // __v19 = __v18 * __v15
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->rotate_rows(vs[19], -1, gk, ss[12]); // __s12 = __v19 >> 1
    info.eval->add(ss[9], ss[11], vs[20]); // __v20 = __s9 + __s11
    info.eval->multiply(vs[20], vs[16], vs[21]); // __v21 = __v20 * __v16
    info.eval->relinearize_inplace(vs[21], rk);
    info.eval->multiply(ss[12], vs[21], vs[22]); // __v22 = __s12 * __v21
    info.eval->relinearize_inplace(vs[22], rk);
    return vs[22];
}
    