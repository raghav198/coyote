
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000000000000000000000000000", info);
    add_bitstring(bits, "0001001000000000000000000000", info);
    add_bitstring(bits, "0000000000000000001000000000", info);
    add_bitstring(bits, "0000001000000000000000000000", info);
    add_bitstring(bits, "1001111100001000000000000000", info);
    add_bitstring(bits, "0000000011000000001000000000", info);
    add_bitstring(bits, "0000011000000000000000000000", info);
    add_bitstring(bits, "0010000000000000001000000000", info);
    add_bitstring(bits, "0000010000000000000000000000", info);
    add_bitstring(bits, "0001000100000000000000000000", info);
    add_bitstring(bits, "0000100000000000000000000000", info);
    add_bitstring(bits, "0010000000000000000000000000", info);
    add_bitstring(bits, "0000000000001000001000000000", info);
    add_bitstring(bits, "0000000000001000000000000000", info);
    add_bitstring(bits, "0000000100000000000000000000", info);
    add_bitstring(bits, "0000000010000000000000000000", info);
    add_bitstring(bits, "1001000100000000000000000000", info);
    add_bitstring(bits, "0000000001000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(49);
    ts[0] = encrypt_input("001101001111000011110000111110011111001111100001111100011011", info);
    ts[1] = encrypt_input("001101101101100011011000111110011111001111100001111000011111", info);
    ts[2] = encrypt_input("0011011001111011010011111000111110000110111111011111000001111100", info);
    ts[3] = encrypt_input("0011111001101111010011111000111110000111111101111110000001111100", info);
    ts[4] = encrypt_input("000000001111000001111100110110111110000011111000", info);
    ts[5] = encrypt_input("000000001101100001111000111100111110000011111000", info);
    ts[6] = encrypt_input("0000000011111000000000111100000000110110", info);
    ts[7] = encrypt_input("0000000011111000000000110110000000111100", info);
    ts[8] = encrypt_input("001101100000111111111000111100000011111000000000", info);
    ts[9] = encrypt_input("001111100000111111101000110110000011111000000000", info);
    ts[16] = encrypt_input("00000000111111111100001111100011111000000000", info);
    ts[17] = encrypt_input("00000000111111111000001111100011111000000000", info);
    ts[20] = encrypt_input("111100011110000110100011111000000000111110000000", info);
    ts[21] = encrypt_input("110110011010000110110011111000000000111110000000", info);
    ts[24] = encrypt_input("00000000000011111000000000000000", info);
    ts[25] = encrypt_input("00000000000011110000000000000000", info);
    ts[26] = encrypt_input("00000000000011110000000000000000", info);
    ts[27] = encrypt_input("00000000000011010000000000000000", info);
    ts[28] = encrypt_input("00000000000011111000000000000000", info);
    ts[29] = encrypt_input("00000000000011110000000000000000", info);
    ts[34] = encrypt_input("00111110000000000000000000000000", info);
    ts[35] = encrypt_input("00111100000000000000000000000000", info);
    ts[38] = encrypt_input("00111100000000000000000000000000", info);
    ts[39] = encrypt_input("00110100000000000000000000000000", info);
    ts[42] = encrypt_input("00111110000000000000000000000000", info);
    ts[43] = encrypt_input("00111100000000000000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[27];
    ctxt ss[17];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -18, gk, ss[0]); // __s0 = __v0 >> 18
    info.eval->rotate_rows(vs[0], -8, gk, ss[1]); // __s1 = __v0 >> 8
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -18, gk, ss[2]); // __s2 = __v1 >> 18
    info.eval->rotate_rows(vs[1], -8, gk, ss[3]); // __s3 = __v1 >> 8
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -18, gk, ss[4]); // __s4 = __v2 >> 18
    info.eval->rotate_rows(vs[2], -8, gk, ss[5]); // __s5 = __v2 >> 8
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -8, gk, ss[6]); // __s6 = __v3 >> 8
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v0@0000000010000000000000000000, __v1@0000000000000000001000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[0], bits["0000000010000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[1], bits["0000000000000000001000000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v1@0000000010000000000000000000, __v4@0000000000000000001000000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[1], bits["0000000010000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[4], bits["0000000000000000001000000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v2@0000000010000000000000000000, __v4@0000000000001000000000000000, __v5@0000000000000000001000000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[2], bits["0000000010000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["0000000000001000000000000000"], t12_2);
    info.eval->multiply_plain(vs[5], bits["0000000000000000001000000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__v4@0000000010000000000000000000, __v0@0000000000001000001000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[4], bits["0000000010000000000000000000"], t13_1);
    info.eval->multiply_plain(vs[0], bits["0000000000001000001000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    
    // __t14 = blend(__v0@0010000000000000000000000000, __v6@0000000010000000000000000000, __v3@0000000000000000001000000000)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(vs[0], bits["0010000000000000000000000000"], t14_1);
    info.eval->multiply_plain(vs[6], bits["0000000010000000000000000000"], t14_2);
    info.eval->multiply_plain(vs[3], bits["0000000000000000001000000000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3}, ts[14]);
    
    
    // __t15 = blend(__v1@0010000000000000000000000000, __v3@0000000010000000000000000000, __v2@0000000000000000001000000000)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(vs[1], bits["0010000000000000000000000000"], t15_1);
    info.eval->multiply_plain(vs[3], bits["0000000010000000000000000000"], t15_2);
    info.eval->multiply_plain(vs[2], bits["0000000000000000001000000000"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[7]); // __v7 = __t14 + __t15
    info.eval->multiply(ts[16], ts[17], vs[8]); // __v8 = __t16 * __t17
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -18, gk, ss[7]); // __s7 = __v8 >> 18
    
    // __t18 = blend(__v7@0010000000000000001000000000, __v5@0000000010000000000000000000, __v4@0000000001000000000000000000, __v6@0000000000001000000000000000)
    ctxt t18_1, t18_2, t18_3, t18_4;
    info.eval->multiply_plain(vs[7], bits["0010000000000000001000000000"], t18_1);
    info.eval->multiply_plain(vs[5], bits["0000000010000000000000000000"], t18_2);
    info.eval->multiply_plain(vs[4], bits["0000000001000000000000000000"], t18_3);
    info.eval->multiply_plain(vs[6], bits["0000000000001000000000000000"], t18_4);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4}, ts[18]);
    
    
    // __t19 = blend(__v4@0010000000000000000000000000, __v8@0000000011000000001000000000, __v1@0000000000001000000000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[4], bits["0010000000000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[8], bits["0000000011000000001000000000"], t19_2);
    info.eval->multiply_plain(vs[1], bits["0000000000001000000000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[9]); // __v9 = __t18 + __t19
    
    // __t22 = blend(__v7@0000000010000000000000000000, __v9@0000000000000000001000000000, __t20@1001000100100000000010000000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[7], bits["0000000010000000000000000000"], t22_1);
    info.eval->multiply_plain(vs[9], bits["0000000000000000001000000000"], t22_2);
    info.eval->add_many({t22_1, t22_2, ts[20]}, ts[22]);
    
    
    // __t23 = blend(__v9@0000000010000000000000000000, __v6@0000000000000000001000000000, __t21@1001000100100000000010000000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(vs[9], bits["0000000010000000000000000000"], t23_1);
    info.eval->multiply_plain(vs[6], bits["0000000000000000001000000000"], t23_2);
    info.eval->add_many({t23_1, t23_2, ts[21]}, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[10]); // __v10 = __t22 * __t23
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -18, gk, ss[8]); // __s8 = __v10 >> 18
    info.eval->rotate_rows(vs[10], -8, gk, ss[9]); // __s9 = __v10 >> 8
    info.eval->multiply(ts[24], ts[25], vs[11]); // __v11 = __t24 * __t25
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->multiply(ts[26], ts[27], vs[12]); // __v12 = __t26 * __t27
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->multiply(ts[28], ts[29], vs[13]); // __v13 = __t28 * __t29
    info.eval->relinearize_inplace(vs[13], rk);
    
    // __t30 = blend(__v10@1001000100000000000000000000, __v0@0000100000000000000000000000, __v1@0000011000000000000000000000, __v12@0000000000001000000000000000)
    ctxt t30_1, t30_2, t30_3, t30_4;
    info.eval->multiply_plain(vs[10], bits["1001000100000000000000000000"], t30_1);
    info.eval->multiply_plain(vs[0], bits["0000100000000000000000000000"], t30_2);
    info.eval->multiply_plain(vs[1], bits["0000011000000000000000000000"], t30_3);
    info.eval->multiply_plain(vs[12], bits["0000000000001000000000000000"], t30_4);
    info.eval->add_many({t30_1, t30_2, t30_3, t30_4}, ts[30]);
    
    
    // __t31 = blend(__s8@1000000000000000000000000000, __s4@0001001000000000000000000000, __s7@0000100000000000000000000000, __s0@0000010000000000000000000000, __s2@0000000100000000000000000000, __v13@0000000000001000000000000000)
    ctxt t31_1, t31_2, t31_3, t31_4, t31_5, t31_6;
    info.eval->multiply_plain(ss[8], bits["1000000000000000000000000000"], t31_1);
    info.eval->multiply_plain(ss[4], bits["0001001000000000000000000000"], t31_2);
    info.eval->multiply_plain(ss[7], bits["0000100000000000000000000000"], t31_3);
    info.eval->multiply_plain(ss[0], bits["0000010000000000000000000000"], t31_4);
    info.eval->multiply_plain(ss[2], bits["0000000100000000000000000000"], t31_5);
    info.eval->multiply_plain(vs[13], bits["0000000000001000000000000000"], t31_6);
    info.eval->add_many({t31_1, t31_2, t31_3, t31_4, t31_5, t31_6}, ts[31]);
    
    info.eval->add(ts[30], ts[31], vs[14]); // __v14 = __t30 + __t31
    
    // __t32 = blend(__v14@1001111100001000000000000000, __v10@0000000010000000000000000000, __v9@0000000001000000000000000000)
    ctxt t32_1, t32_2, t32_3;
    info.eval->multiply_plain(vs[14], bits["1001111100001000000000000000"], t32_1);
    info.eval->multiply_plain(vs[10], bits["0000000010000000000000000000"], t32_2);
    info.eval->multiply_plain(vs[9], bits["0000000001000000000000000000"], t32_3);
    info.eval->add_many({t32_1, t32_2, t32_3}, ts[32]);
    
    
    // __t33 = blend(__s9@1000000000000000000000000000, __s1@0001000100000000000000000000, __s5@0000100000000000000000000000, __s3@0000010000000000000000000000, __s6@0000001000000000000000000000, __s8@0000000010000000000000000000, __s2@0000000001000000000000000000, __v11@0000000000001000000000000000)
    ctxt t33_1, t33_2, t33_3, t33_4, t33_5, t33_6, t33_7, t33_8;
    info.eval->multiply_plain(ss[9], bits["1000000000000000000000000000"], t33_1);
    info.eval->multiply_plain(ss[1], bits["0001000100000000000000000000"], t33_2);
    info.eval->multiply_plain(ss[5], bits["0000100000000000000000000000"], t33_3);
    info.eval->multiply_plain(ss[3], bits["0000010000000000000000000000"], t33_4);
    info.eval->multiply_plain(ss[6], bits["0000001000000000000000000000"], t33_5);
    info.eval->multiply_plain(ss[8], bits["0000000010000000000000000000"], t33_6);
    info.eval->multiply_plain(ss[2], bits["0000000001000000000000000000"], t33_7);
    info.eval->multiply_plain(vs[11], bits["0000000000001000000000000000"], t33_8);
    info.eval->add_many({t33_1, t33_2, t33_3, t33_4, t33_5, t33_6, t33_7, t33_8}, ts[33]);
    
    info.eval->add(ts[32], ts[33], vs[15]); // __v15 = __t32 + __t33
    info.eval->rotate_rows(vs[15], -2, gk, ss[10]); // __s10 = __v15 >> 2
    info.eval->rotate_rows(vs[15], -6, gk, ss[11]); // __s11 = __v15 >> 6
    info.eval->rotate_rows(vs[15], -5, gk, ss[12]); // __s12 = __v15 >> 5
    info.eval->rotate_rows(vs[15], -4, gk, ss[13]); // __s13 = __v15 >> 4
    info.eval->multiply(vs[15], vs[9], vs[16]); // __v16 = __v15 * __v9
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->rotate_rows(vs[16], -18, gk, ss[14]); // __s14 = __v16 >> 18
    
    // __t36 = blend(__v15@0000000001000000000000000000, __t34@0010000000000000000000000000)
    ctxt t36_1;
    info.eval->multiply_plain(vs[15], bits["0000000001000000000000000000"], t36_1);
    info.eval->add(t36_1, ts[34], ts[36]);
    
    
    // __t37 = blend(__s13@0000000001000000000000000000, __t35@0010000000000000000000000000)
    ctxt t37_1;
    info.eval->multiply_plain(ss[13], bits["0000000001000000000000000000"], t37_1);
    info.eval->add(t37_1, ts[35], ts[37]);
    
    info.eval->multiply(ts[36], ts[37], vs[17]); // __v17 = __t36 * __t37
    info.eval->relinearize_inplace(vs[17], rk);
    
    // __t40 = blend(__s11@0000000001000000000000000000, __t38@0010000000000000000000000000)
    ctxt t40_1;
    info.eval->multiply_plain(ss[11], bits["0000000001000000000000000000"], t40_1);
    info.eval->add(t40_1, ts[38], ts[40]);
    
    
    // __t41 = blend(__s12@0000000001000000000000000000, __t39@0010000000000000000000000000)
    ctxt t41_1;
    info.eval->multiply_plain(ss[12], bits["0000000001000000000000000000"], t41_1);
    info.eval->add(t41_1, ts[39], ts[41]);
    
    info.eval->multiply(ts[40], ts[41], vs[18]); // __v18 = __t40 * __t41
    info.eval->relinearize_inplace(vs[18], rk);
    info.eval->multiply(ts[42], ts[43], vs[19]); // __v19 = __t42 * __t43
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->add(vs[18], vs[19], vs[20]); // __v20 = __v18 + __v19
    
    // __t44 = blend(__v20@0010000000000000000000000000, __v18@0000000001000000000000000000)
    ctxt t44_1, t44_2;
    info.eval->multiply_plain(vs[20], bits["0010000000000000000000000000"], t44_1);
    info.eval->multiply_plain(vs[18], bits["0000000001000000000000000000"], t44_2);
    info.eval->add(t44_1, t44_2, ts[44]);
    
    info.eval->add(ts[44], vs[17], vs[21]); // __v21 = __t44 + __v17
    
    // __t45 = blend(__v21@0010000000000000000000000000, __s10@0000000001000000000000000000)
    ctxt t45_1, t45_2;
    info.eval->multiply_plain(vs[21], bits["0010000000000000000000000000"], t45_1);
    info.eval->multiply_plain(ss[10], bits["0000000001000000000000000000"], t45_2);
    info.eval->add(t45_1, t45_2, ts[45]);
    
    
    // __t46 = blend(__s10@0010000000000000000000000000, __v21@0000000001000000000000000000)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(ss[10], bits["0010000000000000000000000000"], t46_1);
    info.eval->multiply_plain(vs[21], bits["0000000001000000000000000000"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    info.eval->multiply(ts[45], ts[46], vs[22]); // __v22 = __t45 * __t46
    info.eval->relinearize_inplace(vs[22], rk);
    info.eval->rotate_rows(vs[22], -27, gk, ss[15]); // __s15 = __v22 >> 27
    info.eval->add(vs[22], ss[14], vs[23]); // __v23 = __v22 + __s14
    
    // __t47 = blend(__v9@0010000000000000000000000000, __s10@0000000010000000000000000000)
    ctxt t47_1, t47_2;
    info.eval->multiply_plain(vs[9], bits["0010000000000000000000000000"], t47_1);
    info.eval->multiply_plain(ss[10], bits["0000000010000000000000000000"], t47_2);
    info.eval->add(t47_1, t47_2, ts[47]);
    
    
    // __t48 = blend(__v23@0010000000000000000000000000, __v15@0000000010000000000000000000)
    ctxt t48_1, t48_2;
    info.eval->multiply_plain(vs[23], bits["0010000000000000000000000000"], t48_1);
    info.eval->multiply_plain(vs[15], bits["0000000010000000000000000000"], t48_2);
    info.eval->add(t48_1, t48_2, ts[48]);
    
    info.eval->multiply(ts[47], ts[48], vs[24]); // __v24 = __t47 * __t48
    info.eval->relinearize_inplace(vs[24], rk);
    info.eval->rotate_rows(vs[24], -6, gk, ss[16]); // __s16 = __v24 >> 6
    info.eval->sub(vs[24], ss[16], vs[25]); // __v25 = __v24 - __s16
    info.eval->add(vs[25], ss[15], vs[26]); // __v26 = __v25 + __s15
    return vs[26];
}
    