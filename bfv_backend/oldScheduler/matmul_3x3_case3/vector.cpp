
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "010000000", info);
    add_bitstring(bits, "000001011", info);
    add_bitstring(bits, "000001110", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "000000001", info);
    add_bitstring(bits, "000100000", info);
    add_bitstring(bits, "000110001", info);
    add_bitstring(bits, "000001001", info);
    add_bitstring(bits, "001000000", info);
    add_bitstring(bits, "010000101", info);
    add_bitstring(bits, "100010000", info);
    add_bitstring(bits, "000001010", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "100000100", info);
    add_bitstring(bits, "110000000", info);
    add_bitstring(bits, "010010000", info);
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "000110000", info);
    add_bitstring(bits, "000000100", info);
    add_bitstring(bits, "000000010", info);
    add_bitstring(bits, "000001100", info);
    add_bitstring(bits, "000100100", info);
    add_bitstring(bits, "010000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(38);
    ts[0] = encrypt_input("111111111111111111101111111111111111111111011011111111111111111110111000000", info);
    ts[1] = encrypt_input("111111111111111111101111111111111111111111011011111111111111111110111000000", info);
    ts[2] = encrypt_input("000001111111111111111111111111111111111111111111110111111111111111111111110", info);
    ts[3] = encrypt_input("000001111111111111111111111111111111111111111111110111111111111111111111110", info);
    ts[4] = encrypt_input("000111111111111111111111111111111111111111111111100011111111111111111111110", info);
    ts[5] = encrypt_input("000111111111111111111111111111111111111111111111100011111111111111111111110", info);
    ts[6] = encrypt_input("000001111111111111111111011101111111111111111111011111111111111111111110110", info);
    ts[7] = encrypt_input("000001111111111111111111011101111111111111111111011111111111111111111110110", info);
    ts[8] = encrypt_input("0011111111111111111111111000000", info);
    ts[9] = encrypt_input("0011111111111111111111111000000", info);
    ts[12] = encrypt_input("01111111111111111111111000111111111111111111111110000", info);
    ts[13] = encrypt_input("01111111111111111111111000111111111111111111111110000", info);
    ts[16] = encrypt_input("000001111111111111111111111101111111111111111111111111111111111111111111110", info);
    ts[17] = encrypt_input("000001111111111111111111111101111111111111111111111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[17];
    ctxt ss[22];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    vs[2] = ts[4]; // vector load instr
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -6, gk, ss[0]); // __s0 = __v3 >> 6
    info.eval->rotate_rows(vs[3], -7, gk, ss[1]); // __s1 = __v3 >> 7
    info.eval->rotate_rows(vs[3], -2, gk, ss[2]); // __s2 = __v3 >> 2
    
    // __t10 = blend(__v0@110000000, __v2@000110001, __v1@000001110, __t8@001000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[0], bits["110000000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["000110001"], t10_2);
    info.eval->multiply_plain(vs[1], bits["000001110"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__s2@110000000, __s1@000100100, __s0@000010000, __v3@000001011, __t9@001000000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[2], bits["110000000"], t11_1);
    info.eval->multiply_plain(ss[1], bits["000100100"], t11_2);
    info.eval->multiply_plain(ss[0], bits["000010000"], t11_3);
    info.eval->multiply_plain(vs[3], bits["000001011"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[3]); // __s3 = __v4 >> 1
    info.eval->rotate_rows(vs[4], -3, gk, ss[4]); // __s4 = __v4 >> 3
    info.eval->rotate_rows(vs[4], -7, gk, ss[5]); // __s5 = __v4 >> 7
    
    // __t14 = blend(__v0@001000000, __t12@010010000)
    ctxt t14_1;
    info.eval->multiply_plain(vs[0], bits["001000000"], t14_1);
    info.eval->add(t14_1, ts[12], ts[14]);
    
    
    // __t15 = blend(__s0@001000000, __t13@010010000)
    ctxt t15_1;
    info.eval->multiply_plain(ss[0], bits["001000000"], t15_1);
    info.eval->add(t15_1, ts[13], ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[5]); // __v5 = __t14 * __t15
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -5, gk, ss[6]); // __s6 = __v5 >> 5
    info.eval->rotate_rows(vs[5], -7, gk, ss[7]); // __s7 = __v5 >> 7
    info.eval->rotate_rows(vs[5], -3, gk, ss[8]); // __s8 = __v5 >> 3
    
    // __t18 = blend(__v0@110000000, __v2@000110000, __v1@000000100, __t16@000001011)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[0], bits["110000000"], t18_1);
    info.eval->multiply_plain(vs[2], bits["000110000"], t18_2);
    info.eval->multiply_plain(vs[1], bits["000000100"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3, ts[16]}, ts[18]);
    
    
    // __t19 = blend(__s6@100000100, __v5@010010000, __s3@000100000, __t17@000001011)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(ss[6], bits["100000100"], t19_1);
    info.eval->multiply_plain(vs[5], bits["010010000"], t19_2);
    info.eval->multiply_plain(ss[3], bits["000100000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3, ts[17]}, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[6]); // __v6 = __t18 * __t19
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -1, gk, ss[9]); // __s9 = __v6 >> 1
    info.eval->rotate_rows(vs[6], -6, gk, ss[10]); // __s10 = __v6 >> 6
    info.eval->rotate_rows(vs[6], -7, gk, ss[11]); // __s11 = __v6 >> 7
    info.eval->rotate_rows(vs[6], -2, gk, ss[12]); // __s12 = __v6 >> 2
    
    // __t20 = blend(__v4@100010000, __s5@000001000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[4], bits["100010000"], t20_1);
    info.eval->multiply_plain(ss[5], bits["000001000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__s7@100000000, __s3@000010000, __v4@000001000)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(ss[7], bits["100000000"], t21_1);
    info.eval->multiply_plain(ss[3], bits["000010000"], t21_2);
    info.eval->multiply_plain(vs[4], bits["000001000"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[7]); // __v7 = __t20 + __t21
    info.eval->rotate_rows(vs[7], -1, gk, ss[13]); // __s13 = __v7 >> 1
    info.eval->rotate_rows(vs[7], -4, gk, ss[14]); // __s14 = __v7 >> 4
    
    // __t22 = blend(__v0@001000000, __v1@000001010, __v2@000000001)
    ctxt t22_1, t22_2, t22_3;
    info.eval->multiply_plain(vs[0], bits["001000000"], t22_1);
    info.eval->multiply_plain(vs[1], bits["000001010"], t22_2);
    info.eval->multiply_plain(vs[2], bits["000000001"], t22_3);
    info.eval->add_many({t22_1, t22_2, t22_3}, ts[22]);
    
    
    // __t23 = blend(__v4@001000000, __s4@000001000, __s8@000000010, __s7@000000001)
    ctxt t23_1, t23_2, t23_3, t23_4;
    info.eval->multiply_plain(vs[4], bits["001000000"], t23_1);
    info.eval->multiply_plain(ss[4], bits["000001000"], t23_2);
    info.eval->multiply_plain(ss[8], bits["000000010"], t23_3);
    info.eval->multiply_plain(ss[7], bits["000000001"], t23_4);
    info.eval->add_many({t23_1, t23_2, t23_3, t23_4}, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[8]); // __v8 = __t22 * __t23
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -7, gk, ss[15]); // __s15 = __v8 >> 7
    info.eval->rotate_rows(vs[8], -2, gk, ss[16]); // __s16 = __v8 >> 2
    info.eval->rotate_rows(vs[8], -5, gk, ss[17]); // __s17 = __v8 >> 5
    
    // __t24 = blend(__v4@010000101, __v6@000010000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[4], bits["010000101"], t24_1);
    info.eval->multiply_plain(vs[6], bits["000010000"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    
    // __t25 = blend(__s13@010000100, __s9@000010000, __s14@000000001)
    ctxt t25_1, t25_2, t25_3;
    info.eval->multiply_plain(ss[13], bits["010000100"], t25_1);
    info.eval->multiply_plain(ss[9], bits["000010000"], t25_2);
    info.eval->multiply_plain(ss[14], bits["000000001"], t25_3);
    info.eval->add_many({t25_1, t25_2, t25_3}, ts[25]);
    
    info.eval->add(ts[24], ts[25], vs[9]); // __v9 = __t24 + __t25
    
    // __t26 = blend(__v0@110000000, __v2@000110001, __v1@000001100)
    ctxt t26_1, t26_2, t26_3;
    info.eval->multiply_plain(vs[0], bits["110000000"], t26_1);
    info.eval->multiply_plain(vs[2], bits["000110001"], t26_2);
    info.eval->multiply_plain(vs[1], bits["000001100"], t26_3);
    info.eval->add_many({t26_1, t26_2, t26_3}, ts[26]);
    
    
    // __t27 = blend(__s12@110000000, __s11@000100100, __s10@000010000, __v6@000001001)
    ctxt t27_1, t27_2, t27_3, t27_4;
    info.eval->multiply_plain(ss[12], bits["110000000"], t27_1);
    info.eval->multiply_plain(ss[11], bits["000100100"], t27_2);
    info.eval->multiply_plain(ss[10], bits["000010000"], t27_3);
    info.eval->multiply_plain(vs[6], bits["000001001"], t27_4);
    info.eval->add_many({t27_1, t27_2, t27_3, t27_4}, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[10]); // __v10 = __t26 * __t27
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -2, gk, ss[18]); // __s18 = __v10 >> 2
    info.eval->rotate_rows(vs[10], -1, gk, ss[19]); // __s19 = __v10 >> 1
    
    // __t28 = blend(__v6@100000000, __s17@000010000, __v8@000000010)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[6], bits["100000000"], t28_1);
    info.eval->multiply_plain(ss[17], bits["000010000"], t28_2);
    info.eval->multiply_plain(vs[8], bits["000000010"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3}, ts[28]);
    
    
    // __t29 = blend(__s15@100000000, __v9@000010000, __s16@000000010)
    ctxt t29_1, t29_2, t29_3;
    info.eval->multiply_plain(ss[15], bits["100000000"], t29_1);
    info.eval->multiply_plain(vs[9], bits["000010000"], t29_2);
    info.eval->multiply_plain(ss[16], bits["000000010"], t29_3);
    info.eval->add_many({t29_1, t29_2, t29_3}, ts[29]);
    
    info.eval->add(ts[28], ts[29], vs[11]); // __v11 = __t28 + __t29
    info.eval->rotate_rows(vs[11], -1, gk, ss[20]); // __s20 = __v11 >> 1
    
    // __t30 = blend(__v0@001000000, __v1@000000010)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(vs[0], bits["001000000"], t30_1);
    info.eval->multiply_plain(vs[1], bits["000000010"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    
    // __t31 = blend(__s10@001000000, __v6@000000010)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(ss[10], bits["001000000"], t31_1);
    info.eval->multiply_plain(vs[6], bits["000000010"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[12]); // __v12 = __t30 * __t31
    info.eval->relinearize_inplace(vs[12], rk);
    
    // __t32 = blend(__v6@010000000, __s19@000001000, __v12@000000010)
    ctxt t32_1, t32_2, t32_3;
    info.eval->multiply_plain(vs[6], bits["010000000"], t32_1);
    info.eval->multiply_plain(ss[19], bits["000001000"], t32_2);
    info.eval->multiply_plain(vs[12], bits["000000010"], t32_3);
    info.eval->add_many({t32_1, t32_2, t32_3}, ts[32]);
    
    
    // __t33 = blend(__s20@010000000, __s18@000001010)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(ss[20], bits["010000000"], t33_1);
    info.eval->multiply_plain(ss[18], bits["000001010"], t33_2);
    info.eval->add(t33_1, t33_2, ts[33]);
    
    info.eval->add(ts[32], ts[33], vs[13]); // __v13 = __t32 + __t33
    info.eval->rotate_rows(vs[13], -3, gk, ss[21]); // __s21 = __v13 >> 3
    info.eval->add(ss[19], vs[13], vs[14]); // __v14 = __s19 + __v13
    
    // __t34 = blend(__s18@001000000, __s9@000000010)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(ss[18], bits["001000000"], t34_1);
    info.eval->multiply_plain(ss[9], bits["000000010"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    
    // __t35 = blend(__v12@001000000, __v11@000000010)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[12], bits["001000000"], t35_1);
    info.eval->multiply_plain(vs[11], bits["000000010"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->add(ts[34], ts[35], vs[15]); // __v15 = __t34 + __t35
    
    // __t36 = blend(__s19@001000000, __v10@000000001)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(ss[19], bits["001000000"], t36_1);
    info.eval->multiply_plain(vs[10], bits["000000001"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    
    // __t37 = blend(__v15@001000000, __s21@000000001)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(vs[15], bits["001000000"], t37_1);
    info.eval->multiply_plain(ss[21], bits["000000001"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    info.eval->add(ts[36], ts[37], vs[16]); // __v16 = __t36 + __t37
    return vs[16];
}
    