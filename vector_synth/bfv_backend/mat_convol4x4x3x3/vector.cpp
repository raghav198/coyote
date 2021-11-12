
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10100000", info);
    add_bitstring(bits, "01100000", info);
    add_bitstring(bits, "00001000", info);
    add_bitstring(bits, "11000000", info);
    add_bitstring(bits, "01000000", info);
    add_bitstring(bits, "10101000", info);
    add_bitstring(bits, "10000000", info);
    add_bitstring(bits, "01001000", info);
    add_bitstring(bits, "01101000", info);
    add_bitstring(bits, "10001000", info);
    add_bitstring(bits, "00100000", info);
    add_bitstring(bits, "11100000", info);
    add_bitstring(bits, "00101000", info);
    add_bitstring(bits, "11001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(50);
    ts[0] = encrypt_input("1111111111110111111111110110101101111011", info);
    ts[1] = encrypt_input("1111111111110111111111110110101101111011", info);
    ts[2] = encrypt_input("11011110101111111011011111111100", info);
    ts[3] = encrypt_input("11011110101111111011011111111100", info);
    ts[4] = encrypt_input("001111100000", info);
    ts[5] = encrypt_input("1111101111100000", info);
    ts[8] = encrypt_input("001111000000", info);
    ts[11] = encrypt_input("000011110000", info);
    ts[12] = encrypt_input("0011111011110000", info);
    ts[15] = encrypt_input("111110000000", info);
    ts[16] = encrypt_input("111110000000", info);
    ts[23] = encrypt_input("1111111111000000", info);
    ts[24] = encrypt_input("11111111111111100000", info);
    ts[28] = encrypt_input("011110000000", info);
    ts[29] = encrypt_input("1111111111000000", info);
    ts[38] = encrypt_input("111101111111110011111000", info);
    ts[39] = encrypt_input("111111111111110011111000", info);
    ts[40] = encrypt_input("0011111011111000", info);
    ts[41] = encrypt_input("11111011111011111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[22];
    ctxt ss[14];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -4, gk, ss[2]); // __s2 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -7, gk, ss[3]); // __s3 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -5, gk, ss[4]); // __s4 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -6, gk, ss[5]); // __s5 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -3, gk, ss[6]); // __s6 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[7]); // __s7 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -2, gk, ss[8]); // __s8 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -4, gk, ss[9]); // __s9 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -3, gk, ss[10]); // __s10 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -7, gk, ss[11]); // __s11 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -6, gk, ss[12]); // __s12 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -5, gk, ss[13]); // __s13 = __v1 >> 5
    
    // __t6 = blend(__s8@10000000, __v1@01000000, __s12@00001000, __t4@00100000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[8], bits["10000000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["01000000"], t6_2);
    info.eval->multiply_plain(ss[12], bits["00001000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__s1@01000000, __v0@00001000, __t5@10100000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[1], bits["01000000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["00001000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t9 = blend(__s11@10000000, __s7@01000000, __s9@00101000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[11], bits["10000000"], t9_1);
    info.eval->multiply_plain(ss[7], bits["01000000"], t9_2);
    info.eval->multiply_plain(ss[9], bits["00101000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    
    // __t10 = blend(__s4@10001000, __s6@01000000, __t8@00100000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[4], bits["10001000"], t10_1);
    info.eval->multiply_plain(ss[6], bits["01000000"], t10_2);
    info.eval->add_many({t10_1, t10_2, ts[8]}, ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[3]); // __v3 = __t9 * __t10
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[2], vs[3], vs[4]); // __v4 = __v2 + __v3
    
    // __t13 = blend(__v1@10000000, __s12@01000000, __s13@00100000, __t11@00001000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[1], bits["10000000"], t13_1);
    info.eval->multiply_plain(ss[12], bits["01000000"], t13_2);
    info.eval->multiply_plain(ss[13], bits["00100000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3, ts[11]}, ts[13]);
    
    
    // __t14 = blend(__v0@10000000, __s3@01000000, __t12@00101000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[0], bits["10000000"], t14_1);
    info.eval->multiply_plain(ss[3], bits["01000000"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[12]}, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[5]); // __v5 = __t13 * __t14
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t17 = blend(__s10@01001000, __s7@00100000, __t15@10000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[10], bits["01001000"], t17_1);
    info.eval->multiply_plain(ss[7], bits["00100000"], t17_2);
    info.eval->add_many({t17_1, t17_2, ts[15]}, ts[17]);
    
    
    // __t18 = blend(__s5@01100000, __s3@00001000, __t16@10000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[5], bits["01100000"], t18_1);
    info.eval->multiply_plain(ss[3], bits["00001000"], t18_2);
    info.eval->add_many({t18_1, t18_2, ts[16]}, ts[18]);
    
    info.eval->multiply(ts[17], ts[18], vs[6]); // __v6 = __t17 * __t18
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t19 = blend(__v3@10000000, __v4@01000000, __v6@00001000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[3], bits["10000000"], t19_1);
    info.eval->multiply_plain(vs[4], bits["01000000"], t19_2);
    info.eval->multiply_plain(vs[6], bits["00001000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    
    // __t20 = blend(__v5@11000000, __v3@00001000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[5], bits["11000000"], t20_1);
    info.eval->multiply_plain(vs[3], bits["00001000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    info.eval->add(ts[19], ts[20], vs[7]); // __v7 = __t19 + __t20
    
    // __t21 = blend(__s13@10000000, __s11@01101000)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(ss[13], bits["10000000"], t21_1);
    info.eval->multiply_plain(ss[11], bits["01101000"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    
    // __t22 = blend(__s3@10000000, __s0@01000000, __s1@00100000, __s2@00001000)
    ctxt t22_1, t22_2, t22_3, t22_4;
    info.eval->multiply_plain(ss[3], bits["10000000"], t22_1);
    info.eval->multiply_plain(ss[0], bits["01000000"], t22_2);
    info.eval->multiply_plain(ss[1], bits["00100000"], t22_3);
    info.eval->multiply_plain(ss[2], bits["00001000"], t22_4);
    info.eval->add_many({t22_1, t22_2, t22_3, t22_4}, ts[22]);
    
    info.eval->multiply(ts[21], ts[22], vs[8]); // __v8 = __t21 * __t22
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t25 = blend(__v1@00100000, __s7@00001000, __t23@11000000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(vs[1], bits["00100000"], t25_1);
    info.eval->multiply_plain(ss[7], bits["00001000"], t25_2);
    info.eval->add_many({t25_1, t25_2, ts[23]}, ts[25]);
    
    
    // __t26 = blend(__s5@00001000, __t24@11100000)
    ctxt t26_1;
    info.eval->multiply_plain(ss[5], bits["00001000"], t26_1);
    info.eval->add(t26_1, ts[24], ts[26]);
    
    info.eval->multiply(ts[25], ts[26], vs[9]); // __v9 = __t25 * __t26
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t27 = blend(__v8@10000000, __v6@01000000, __v9@00001000)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(vs[8], bits["10000000"], t27_1);
    info.eval->multiply_plain(vs[6], bits["01000000"], t27_2);
    info.eval->multiply_plain(vs[9], bits["00001000"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3}, ts[27]);
    
    info.eval->add(vs[7], ts[27], vs[10]); // __v10 = __v7 + __t27
    
    // __t30 = blend(__s12@10000000, __s8@00101000, __t28@01000000)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(ss[12], bits["10000000"], t30_1);
    info.eval->multiply_plain(ss[8], bits["00101000"], t30_2);
    info.eval->add_many({t30_1, t30_2, ts[28]}, ts[30]);
    
    
    // __t31 = blend(__s3@00100000, __s0@00001000, __t29@11000000)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(ss[3], bits["00100000"], t31_1);
    info.eval->multiply_plain(ss[0], bits["00001000"], t31_2);
    info.eval->add_many({t31_1, t31_2, ts[29]}, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[11]); // __v11 = __t30 * __t31
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t32 = blend(__v10@01001000, __v6@00100000)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(vs[10], bits["01001000"], t32_1);
    info.eval->multiply_plain(vs[6], bits["00100000"], t32_2);
    info.eval->add(t32_1, t32_2, ts[32]);
    
    
    // __t33 = blend(__v8@01000000, __v11@00100000, __v2@00001000)
    ctxt t33_1, t33_2, t33_3;
    info.eval->multiply_plain(vs[8], bits["01000000"], t33_1);
    info.eval->multiply_plain(vs[11], bits["00100000"], t33_2);
    info.eval->multiply_plain(vs[2], bits["00001000"], t33_3);
    info.eval->add_many({t33_1, t33_2, t33_3}, ts[33]);
    
    info.eval->add(ts[32], ts[33], vs[12]); // __v12 = __t32 + __t33
    
    // __t34 = blend(__v8@00100000, __v11@00001000)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[8], bits["00100000"], t34_1);
    info.eval->multiply_plain(vs[11], bits["00001000"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    info.eval->add(vs[12], ts[34], vs[13]); // __v13 = __v12 + __t34
    
    // __t35 = blend(__v10@10000000, __v13@00101000)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[10], bits["10000000"], t35_1);
    info.eval->multiply_plain(vs[13], bits["00101000"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    
    // __t36 = blend(__v2@10000000, __v3@00100000, __v8@00001000)
    ctxt t36_1, t36_2, t36_3;
    info.eval->multiply_plain(vs[2], bits["10000000"], t36_1);
    info.eval->multiply_plain(vs[3], bits["00100000"], t36_2);
    info.eval->multiply_plain(vs[8], bits["00001000"], t36_3);
    info.eval->add_many({t36_1, t36_2, t36_3}, ts[36]);
    
    info.eval->add(ts[35], ts[36], vs[14]); // __v14 = __t35 + __t36
    
    // __t37 = blend(__v11@10000000, __v9@00100000, __v5@00001000)
    ctxt t37_1, t37_2, t37_3;
    info.eval->multiply_plain(vs[11], bits["10000000"], t37_1);
    info.eval->multiply_plain(vs[9], bits["00100000"], t37_2);
    info.eval->multiply_plain(vs[5], bits["00001000"], t37_3);
    info.eval->add_many({t37_1, t37_2, t37_3}, ts[37]);
    
    info.eval->add(vs[14], ts[37], vs[15]); // __v15 = __v14 + __t37
    info.eval->multiply(ts[38], ts[39], vs[16]); // __v16 = __t38 * __t39
    info.eval->relinearize_inplace(vs[16], rk);
    
    // __t42 = blend(__s10@10000000, __s9@01000000, __t40@00101000)
    ctxt t42_1, t42_2;
    info.eval->multiply_plain(ss[10], bits["10000000"], t42_1);
    info.eval->multiply_plain(ss[9], bits["01000000"], t42_2);
    info.eval->add_many({t42_1, t42_2, ts[40]}, ts[42]);
    
    
    // __t43 = blend(__v0@01000000, __t41@10101000)
    ctxt t43_1;
    info.eval->multiply_plain(vs[0], bits["01000000"], t43_1);
    info.eval->add(t43_1, ts[41], ts[43]);
    
    info.eval->multiply(ts[42], ts[43], vs[17]); // __v17 = __t42 * __t43
    info.eval->relinearize_inplace(vs[17], rk);
    
    // __t44 = blend(__v15@10101000, __v12@01000000)
    ctxt t44_1, t44_2;
    info.eval->multiply_plain(vs[15], bits["10101000"], t44_1);
    info.eval->multiply_plain(vs[12], bits["01000000"], t44_2);
    info.eval->add(t44_1, t44_2, ts[44]);
    
    
    // __t45 = blend(__v17@11001000, __v5@00100000)
    ctxt t45_1, t45_2;
    info.eval->multiply_plain(vs[17], bits["11001000"], t45_1);
    info.eval->multiply_plain(vs[5], bits["00100000"], t45_2);
    info.eval->add(t45_1, t45_2, ts[45]);
    
    info.eval->add(ts[44], ts[45], vs[18]); // __v18 = __t44 + __t45
    
    // __t46 = blend(__v16@10100000, __v11@01000000)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(vs[16], bits["10100000"], t46_1);
    info.eval->multiply_plain(vs[11], bits["01000000"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    info.eval->add(vs[18], ts[46], vs[19]); // __v19 = __v18 + __t46
    
    // __t47 = blend(__v6@10000000, __v9@01000000, __v2@00100000)
    ctxt t47_1, t47_2, t47_3;
    info.eval->multiply_plain(vs[6], bits["10000000"], t47_1);
    info.eval->multiply_plain(vs[9], bits["01000000"], t47_2);
    info.eval->multiply_plain(vs[2], bits["00100000"], t47_3);
    info.eval->add_many({t47_1, t47_2, t47_3}, ts[47]);
    
    info.eval->add(vs[19], ts[47], vs[20]); // __v20 = __v19 + __t47
    
    // __t48 = blend(__v20@11100000, __v18@00001000)
    ctxt t48_1, t48_2;
    info.eval->multiply_plain(vs[20], bits["11100000"], t48_1);
    info.eval->multiply_plain(vs[18], bits["00001000"], t48_2);
    info.eval->add(t48_1, t48_2, ts[48]);
    
    
    // __t49 = blend(__v9@10000000, __v16@01001000, __v17@00100000)
    ctxt t49_1, t49_2, t49_3;
    info.eval->multiply_plain(vs[9], bits["10000000"], t49_1);
    info.eval->multiply_plain(vs[16], bits["01001000"], t49_2);
    info.eval->multiply_plain(vs[17], bits["00100000"], t49_3);
    info.eval->add_many({t49_1, t49_2, t49_3}, ts[49]);
    
    info.eval->add(ts[48], ts[49], vs[21]); // __v21 = __t48 + __t49
    return vs[21];
}
    