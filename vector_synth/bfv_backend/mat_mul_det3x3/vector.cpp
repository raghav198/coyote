
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00001010000", info);
    add_bitstring(bits, "11101011001", info);
    add_bitstring(bits, "00000010000", info);
    add_bitstring(bits, "00000101000", info);
    add_bitstring(bits, "00000000100", info);
    add_bitstring(bits, "10000000000", info);
    add_bitstring(bits, "00010100011", info);
    add_bitstring(bits, "00000000001", info);
    add_bitstring(bits, "01000000000", info);
    add_bitstring(bits, "00010010000", info);
    add_bitstring(bits, "10100000000", info);
    add_bitstring(bits, "11100000001", info);
    add_bitstring(bits, "00010000110", info);
    add_bitstring(bits, "01000001000", info);
    add_bitstring(bits, "00000000010", info);
    add_bitstring(bits, "00000100010", info);
    add_bitstring(bits, "00010001000", info);
    add_bitstring(bits, "11100000000", info);
    add_bitstring(bits, "00000001000", info);
    add_bitstring(bits, "00000000101", info);
    add_bitstring(bits, "00001000000", info);
    add_bitstring(bits, "00010010100", info);
    add_bitstring(bits, "00000100000", info);
    add_bitstring(bits, "00010001001", info);
    add_bitstring(bits, "01000010000", info);
    add_bitstring(bits, "00100000000", info);
    add_bitstring(bits, "00010000000", info);
    add_bitstring(bits, "00000010001", info);
    add_bitstring(bits, "00001000011", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(51);
    ts[0] = encrypt_input("00111110111111101111110011010110110", info);
    ts[1] = encrypt_input("00111110111111101111110011010110110", info);
    ts[2] = encrypt_input("11111011111001101111110110110110100", info);
    ts[3] = encrypt_input("11111011111001101111110110110110100", info);
    ts[4] = encrypt_input("01111100000011110011110", info);
    ts[5] = encrypt_input("000011110000000", info);
    ts[8] = encrypt_input("00111110011111001111100", info);
    ts[9] = encrypt_input("0000011110011111000", info);
    ts[12] = encrypt_input("000001111000000", info);
    ts[16] = encrypt_input("000001111100000", info);
    ts[17] = encrypt_input("0000001111100011111", info);
    ts[22] = encrypt_input("01111111111000000011111", info);
    ts[23] = encrypt_input("11111111111111111110000011111011111", info);
    ts[26] = encrypt_input("011110111100000011111011111", info);
    ts[27] = encrypt_input("0000000011111111110", info);
    ts[36] = encrypt_input("000001111000000", info);
    ts[41] = encrypt_input("000001111100000", info);
    ts[42] = encrypt_input("000001111000000", info);
    ts[43] = encrypt_input("000001111100000", info);
    ts[44] = encrypt_input("000001111000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[29];
    ctxt ss[32];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -6, gk, ss[1]); // __s1 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -7, gk, ss[2]); // __s2 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -8, gk, ss[3]); // __s3 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -9, gk, ss[4]); // __s4 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -4, gk, ss[5]); // __s5 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -5, gk, ss[6]); // __s6 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -10, gk, ss[7]); // __s7 = __v0 >> 10
    info.eval->rotate_rows(vs[0], -2, gk, ss[8]); // __s8 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -3, gk, ss[9]); // __s9 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -2, gk, ss[10]); // __s10 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -6, gk, ss[11]); // __s11 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -8, gk, ss[12]); // __s12 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -10, gk, ss[13]); // __s13 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -5, gk, ss[14]); // __s14 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -7, gk, ss[15]); // __s15 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -3, gk, ss[16]); // __s16 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -4, gk, ss[17]); // __s17 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -9, gk, ss[18]); // __s18 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -1, gk, ss[19]); // __s19 = __v1 >> 1
    
    // __t6 = blend(__s3@00010000000, __s1@00001000000, __s4@00000010000, __s8@00000001000, __t4@01000000101)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[3], bits["00010000000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["00001000000"], t6_2);
    info.eval->multiply_plain(ss[4], bits["00000010000"], t6_3);
    info.eval->multiply_plain(ss[8], bits["00000001000"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__s13@01000010000, __s14@00010001001, __s19@00000000100, __t5@00001000000)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(ss[13], bits["01000010000"], t7_1);
    info.eval->multiply_plain(ss[14], bits["00010001001"], t7_2);
    info.eval->multiply_plain(ss[19], bits["00000000100"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t10 = blend(__s2@10000000000, __s4@00000001000, __s1@00000000001, __t8@00100100100)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[2], bits["10000000000"], t10_1);
    info.eval->multiply_plain(ss[4], bits["00000001000"], t10_2);
    info.eval->multiply_plain(ss[1], bits["00000000001"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__v1@10000000000, __s10@00100000000, __s12@00000000100, __s13@00000000001, __t9@00000101000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(vs[1], bits["10000000000"], t11_1);
    info.eval->multiply_plain(ss[10], bits["00100000000"], t11_2);
    info.eval->multiply_plain(ss[12], bits["00000000100"], t11_3);
    info.eval->multiply_plain(ss[13], bits["00000000001"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t13 = blend(__s5@00000000101, __s9@00000000010, __t12@00000100000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[5], bits["00000000101"], t13_1);
    info.eval->multiply_plain(ss[9], bits["00000000010"], t13_2);
    info.eval->add_many({t13_1, t13_2, ts[12]}, ts[13]);
    
    
    // __t14 = blend(__s15@00000100000, __s11@00000000100, __s17@00000000010, __s16@00000000001)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(ss[15], bits["00000100000"], t14_1);
    info.eval->multiply_plain(ss[11], bits["00000000100"], t14_2);
    info.eval->multiply_plain(ss[17], bits["00000000010"], t14_3);
    info.eval->multiply_plain(ss[16], bits["00000000001"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[4]); // __v4 = __t13 * __t14
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t15 = blend(__v2@00000000100, __v4@00000000001)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[2], bits["00000000100"], t15_1);
    info.eval->multiply_plain(vs[4], bits["00000000001"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->add(ts[15], vs[3], vs[5]); // __v5 = __t15 + __v3
    
    // __t18 = blend(__s7@00010001000, __s3@00000010001, __s8@00000000100, __s6@00000000010, __t16@00000100000)
    ctxt t18_1, t18_2, t18_3, t18_4;
    info.eval->multiply_plain(ss[7], bits["00010001000"], t18_1);
    info.eval->multiply_plain(ss[3], bits["00000010001"], t18_2);
    info.eval->multiply_plain(ss[8], bits["00000000100"], t18_3);
    info.eval->multiply_plain(ss[6], bits["00000000010"], t18_4);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4, ts[16]}, ts[18]);
    
    
    // __t19 = blend(__s12@00010000000, __s13@00000100000, __s10@00000001000, __s16@00000000100, __s15@00000000010, __t17@00000010001)
    ctxt t19_1, t19_2, t19_3, t19_4, t19_5;
    info.eval->multiply_plain(ss[12], bits["00010000000"], t19_1);
    info.eval->multiply_plain(ss[13], bits["00000100000"], t19_2);
    info.eval->multiply_plain(ss[10], bits["00000001000"], t19_3);
    info.eval->multiply_plain(ss[16], bits["00000000100"], t19_4);
    info.eval->multiply_plain(ss[15], bits["00000000010"], t19_5);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4, t19_5, ts[17]}, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[6]); // __v6 = __t18 * __t19
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t20 = blend(__v2@00010000000, __v4@00000100010, __v6@00000000100, __v5@00000000001)
    ctxt t20_1, t20_2, t20_3, t20_4;
    info.eval->multiply_plain(vs[2], bits["00010000000"], t20_1);
    info.eval->multiply_plain(vs[4], bits["00000100010"], t20_2);
    info.eval->multiply_plain(vs[6], bits["00000000100"], t20_3);
    info.eval->multiply_plain(vs[5], bits["00000000001"], t20_4);
    info.eval->add_many({t20_1, t20_2, t20_3, t20_4}, ts[20]);
    
    
    // __t21 = blend(__v6@00010100011, __v4@00000000100)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[6], bits["00010100011"], t21_1);
    info.eval->multiply_plain(vs[4], bits["00000000100"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[7]); // __v7 = __t20 + __t21
    
    // __t24 = blend(__s4@10000000000, __s0@00010010000, __s2@00001000000, __s1@00000000100, __t22@01100000001)
    ctxt t24_1, t24_2, t24_3, t24_4;
    info.eval->multiply_plain(ss[4], bits["10000000000"], t24_1);
    info.eval->multiply_plain(ss[0], bits["00010010000"], t24_2);
    info.eval->multiply_plain(ss[2], bits["00001000000"], t24_3);
    info.eval->multiply_plain(ss[1], bits["00000000100"], t24_4);
    info.eval->add_many({t24_1, t24_2, t24_3, t24_4, ts[22]}, ts[24]);
    
    
    // __t25 = blend(__s11@00001010000, __t23@11110000101)
    ctxt t25_1;
    info.eval->multiply_plain(ss[11], bits["00001010000"], t25_1);
    info.eval->add(t25_1, ts[23], ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[8]); // __v8 = __t24 * __t25
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t28 = blend(__s6@10000000000, __s7@00001000000, __s2@00000000010, __t26@01100000101)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(ss[6], bits["10000000000"], t28_1);
    info.eval->multiply_plain(ss[7], bits["00001000000"], t28_2);
    info.eval->multiply_plain(ss[2], bits["00000000010"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3, ts[26]}, ts[28]);
    
    
    // __t29 = blend(__s17@10000000000, __s15@01000000000, __s11@00100000000, __s18@00001000000, __s12@00000000001, __t27@00000000110)
    ctxt t29_1, t29_2, t29_3, t29_4, t29_5;
    info.eval->multiply_plain(ss[17], bits["10000000000"], t29_1);
    info.eval->multiply_plain(ss[15], bits["01000000000"], t29_2);
    info.eval->multiply_plain(ss[11], bits["00100000000"], t29_3);
    info.eval->multiply_plain(ss[18], bits["00001000000"], t29_4);
    info.eval->multiply_plain(ss[12], bits["00000000001"], t29_5);
    info.eval->add_many({t29_1, t29_2, t29_3, t29_4, t29_5, ts[27]}, ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[9]); // __v9 = __t28 * __t29
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t30 = blend(__v9@11100000000, __v7@00010000110, __v8@00001000000, __v2@00000010001, __v6@00000001000)
    ctxt t30_1, t30_2, t30_3, t30_4, t30_5;
    info.eval->multiply_plain(vs[9], bits["11100000000"], t30_1);
    info.eval->multiply_plain(vs[7], bits["00010000110"], t30_2);
    info.eval->multiply_plain(vs[8], bits["00001000000"], t30_3);
    info.eval->multiply_plain(vs[2], bits["00000010001"], t30_4);
    info.eval->multiply_plain(vs[6], bits["00000001000"], t30_5);
    info.eval->add_many({t30_1, t30_2, t30_3, t30_4, t30_5}, ts[30]);
    
    
    // __t31 = blend(__v3@10100000000, __v2@01000001000, __v8@00010010100, __v9@00001000011)
    ctxt t31_1, t31_2, t31_3, t31_4;
    info.eval->multiply_plain(vs[3], bits["10100000000"], t31_1);
    info.eval->multiply_plain(vs[2], bits["01000001000"], t31_2);
    info.eval->multiply_plain(vs[8], bits["00010010100"], t31_3);
    info.eval->multiply_plain(vs[9], bits["00001000011"], t31_4);
    info.eval->add_many({t31_1, t31_2, t31_3, t31_4}, ts[31]);
    
    info.eval->add(ts[30], ts[31], vs[10]); // __v10 = __t30 + __t31
    info.eval->rotate_rows(vs[10], -9, gk, ss[20]); // __s20 = __v10 >> 9
    info.eval->rotate_rows(vs[10], -7, gk, ss[21]); // __s21 = __v10 >> 7
    
    // __t32 = blend(__v10@11101011001, __v7@00000100000, __v5@00000000100)
    ctxt t32_1, t32_2, t32_3;
    info.eval->multiply_plain(vs[10], bits["11101011001"], t32_1);
    info.eval->multiply_plain(vs[7], bits["00000100000"], t32_2);
    info.eval->multiply_plain(vs[5], bits["00000000100"], t32_3);
    info.eval->add_many({t32_1, t32_2, t32_3}, ts[32]);
    
    
    // __t33 = blend(__v8@11100000001, __v2@00001000000, __v3@00000101000, __v6@00000010000, __v9@00000000100)
    ctxt t33_1, t33_2, t33_3, t33_4, t33_5;
    info.eval->multiply_plain(vs[8], bits["11100000001"], t33_1);
    info.eval->multiply_plain(vs[2], bits["00001000000"], t33_2);
    info.eval->multiply_plain(vs[3], bits["00000101000"], t33_3);
    info.eval->multiply_plain(vs[6], bits["00000010000"], t33_4);
    info.eval->multiply_plain(vs[9], bits["00000000100"], t33_5);
    info.eval->add_many({t33_1, t33_2, t33_3, t33_4, t33_5}, ts[33]);
    
    info.eval->add(ts[32], ts[33], vs[11]); // __v11 = __t32 + __t33
    info.eval->rotate_rows(vs[11], -1, gk, ss[22]); // __s22 = __v11 >> 1
    info.eval->rotate_rows(vs[11], -4, gk, ss[23]); // __s23 = __v11 >> 4
    info.eval->rotate_rows(vs[11], -10, gk, ss[24]); // __s24 = __v11 >> 10
    info.eval->rotate_rows(vs[11], -7, gk, ss[25]); // __s25 = __v11 >> 7
    info.eval->rotate_rows(vs[11], -5, gk, ss[26]); // __s26 = __v11 >> 5
    
    // __t34 = blend(__v11@00000000100, __v7@00000000001)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[11], bits["00000000100"], t34_1);
    info.eval->multiply_plain(vs[7], bits["00000000001"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    
    // __t35 = blend(__v10@00000000100, __v11@00000000001)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[10], bits["00000000100"], t35_1);
    info.eval->multiply_plain(vs[11], bits["00000000001"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[12]); // __v12 = __t34 * __t35
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -7, gk, ss[27]); // __s27 = __v12 >> 7
    info.eval->rotate_rows(vs[12], -5, gk, ss[28]); // __s28 = __v12 >> 5
    
    // __t37 = blend(__s20@01000000000, __t36@00000100000)
    ctxt t37_1;
    info.eval->multiply_plain(ss[20], bits["01000000000"], t37_1);
    info.eval->add(t37_1, ts[36], ts[37]);
    
    
    // __t38 = blend(__s24@01000000000, __s15@00000100000)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(ss[24], bits["01000000000"], t38_1);
    info.eval->multiply_plain(ss[15], bits["00000100000"], t38_2);
    info.eval->add(t38_1, t38_2, ts[38]);
    
    info.eval->multiply(ts[37], ts[38], vs[13]); // __v13 = __t37 * __t38
    info.eval->relinearize_inplace(vs[13], rk);
    
    // __t39 = blend(__s25@01000000000, __v0@00000100000)
    ctxt t39_1, t39_2;
    info.eval->multiply_plain(ss[25], bits["01000000000"], t39_1);
    info.eval->multiply_plain(vs[0], bits["00000100000"], t39_2);
    info.eval->add(t39_1, t39_2, ts[39]);
    
    
    // __t40 = blend(__s22@01000000000, __s13@00000100000)
    ctxt t40_1, t40_2;
    info.eval->multiply_plain(ss[22], bits["01000000000"], t40_1);
    info.eval->multiply_plain(ss[13], bits["00000100000"], t40_2);
    info.eval->add(t40_1, t40_2, ts[40]);
    
    info.eval->multiply(ts[39], ts[40], vs[14]); // __v14 = __t39 * __t40
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->multiply(ts[41], ts[42], vs[15]); // __v15 = __t41 * __t42
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->multiply(vs[0], ss[15], vs[16]); // __v16 = __v0 * __s15
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->add(vs[16], vs[14], vs[17]); // __v17 = __v16 + __v14
    info.eval->multiply(ts[43], ss[13], vs[18]); // __v18 = __t43 * __s13
    info.eval->relinearize_inplace(vs[18], rk);
    info.eval->multiply(vs[0], ts[44], vs[19]); // __v19 = __v0 * __t44
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->add(vs[13], vs[18], vs[20]); // __v20 = __v13 + __v18
    
    // __t45 = blend(__v13@01000000000, __v20@00000100000)
    ctxt t45_1, t45_2;
    info.eval->multiply_plain(vs[13], bits["01000000000"], t45_1);
    info.eval->multiply_plain(vs[20], bits["00000100000"], t45_2);
    info.eval->add(t45_1, t45_2, ts[45]);
    
    
    // __t46 = blend(__v14@01000000000, __v15@00000100000)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(vs[14], bits["01000000000"], t46_1);
    info.eval->multiply_plain(vs[15], bits["00000100000"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    info.eval->add(ts[45], ts[46], vs[21]); // __v21 = __t45 + __t46
    
    // __t47 = blend(__s28@00001000000, __v17@00000100000)
    ctxt t47_1, t47_2;
    info.eval->multiply_plain(ss[28], bits["00001000000"], t47_1);
    info.eval->multiply_plain(vs[17], bits["00000100000"], t47_2);
    info.eval->add(t47_1, t47_2, ts[47]);
    
    
    // __t48 = blend(__s27@00001000000, __v19@00000100000)
    ctxt t48_1, t48_2;
    info.eval->multiply_plain(ss[27], bits["00001000000"], t48_1);
    info.eval->multiply_plain(vs[19], bits["00000100000"], t48_2);
    info.eval->add(t48_1, t48_2, ts[48]);
    
    info.eval->add(ts[47], ts[48], vs[22]); // __v22 = __t47 + __t48
    info.eval->multiply(vs[22], ss[23], vs[23]); // __v23 = __v22 * __s23
    info.eval->relinearize_inplace(vs[23], rk);
    info.eval->multiply(vs[21], ss[21], vs[24]); // __v24 = __v21 * __s21
    info.eval->relinearize_inplace(vs[24], rk);
    info.eval->add(vs[23], vs[24], vs[25]); // __v25 = __v23 + __v24
    
    // __t49 = blend(__s26@01000000000, __v11@00001000000, __s24@00000100000)
    ctxt t49_1, t49_2, t49_3;
    info.eval->multiply_plain(ss[26], bits["01000000000"], t49_1);
    info.eval->multiply_plain(vs[11], bits["00001000000"], t49_2);
    info.eval->multiply_plain(ss[24], bits["00000100000"], t49_3);
    info.eval->add_many({t49_1, t49_2, t49_3}, ts[49]);
    
    
    // __t50 = blend(__v21@01000000000, __v22@00001000000, __v25@00000100000)
    ctxt t50_1, t50_2, t50_3;
    info.eval->multiply_plain(vs[21], bits["01000000000"], t50_1);
    info.eval->multiply_plain(vs[22], bits["00001000000"], t50_2);
    info.eval->multiply_plain(vs[25], bits["00000100000"], t50_3);
    info.eval->add_many({t50_1, t50_2, t50_3}, ts[50]);
    
    info.eval->multiply(ts[49], ts[50], vs[26]); // __v26 = __t49 * __t50
    info.eval->relinearize_inplace(vs[26], rk);
    info.eval->rotate_rows(vs[26], -10, gk, ss[29]); // __s29 = __v26 >> 10
    info.eval->rotate_rows(vs[26], -7, gk, ss[30]); // __s30 = __v26 >> 7
    info.eval->rotate_rows(vs[26], -6, gk, ss[31]); // __s31 = __v26 >> 6
    info.eval->sub(ss[30], ss[31], vs[27]); // __v27 = __s30 - __s31
    info.eval->add(vs[27], ss[29], vs[28]); // __v28 = __v27 + __s29
    return vs[28];
}
    