
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "110000000", info);
    add_bitstring(bits, "000000101", info);
    add_bitstring(bits, "001000000", info);
    add_bitstring(bits, "010010000", info);
    add_bitstring(bits, "001001000", info);
    add_bitstring(bits, "001101000", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "000000010", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "000000001", info);
    add_bitstring(bits, "010000000", info);
    add_bitstring(bits, "000000100", info);
    add_bitstring(bits, "000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(61);
    ts[0] = encrypt_input("00111111111111111111100110000000", info);
    ts[1] = encrypt_input("00111111111111111111100110000000", info);
    ts[2] = encrypt_input("00001111111111111111111011100000", info);
    ts[3] = encrypt_input("00001111111111111111111011100000", info);
    ts[4] = encrypt_input("00111111111111111111101110000000", info);
    ts[5] = encrypt_input("00111111111111111111101110000000", info);
    ts[6] = encrypt_input("00001111111111111111111101100000", info);
    ts[7] = encrypt_input("00001111111111111111111101100000", info);
    ts[8] = encrypt_input("00000011111111111111111111111000", info);
    ts[9] = encrypt_input("00000011111111111111111111111000", info);
    ts[10] = encrypt_input("00011111111111111111111111000000", info);
    ts[11] = encrypt_input("00011111111111111111111111000000", info);
    ts[12] = encrypt_input("00000000111111111111111111110110", info);
    ts[13] = encrypt_input("00000000111111111111111111110110", info);
    ts[14] = encrypt_input("00000001111111111111111111111100", info);
    ts[15] = encrypt_input("00000001111111111111111111111100", info);
    ts[16] = encrypt_input("00000111111111111111111111110000", info);
    ts[17] = encrypt_input("00000111111111111111111111110000", info);
    ts[18] = encrypt_input("00011111111111111111110011000000", info);
    ts[19] = encrypt_input("00011111111111111111110011000000", info);
    ts[20] = encrypt_input("00001111111111111111111011100000", info);
    ts[21] = encrypt_input("00001111111111111111111011100000", info);
    ts[26] = encrypt_input("00001111111111111111111011100000", info);
    ts[27] = encrypt_input("00001111111111111111111011100000", info);
    ts[28] = encrypt_input("00000001111111111111111111101100", info);
    ts[29] = encrypt_input("00000001111111111111111111101100", info);
    ts[32] = encrypt_input("00000001111111111111111111111100", info);
    ts[33] = encrypt_input("00000001111111111111111111111100", info);
    ts[36] = encrypt_input("00001111111111111111111111100000", info);
    ts[37] = encrypt_input("00001111111111111111111111100000", info);
    ts[40] = encrypt_input("00000111111111111111111110110000", info);
    ts[41] = encrypt_input("00000111111111111111111110110000", info);
    ts[46] = encrypt_input("00111111111111111111111110000000", info);
    ts[47] = encrypt_input("00111111111111111111111110000000", info);
    ts[48] = encrypt_input("00011111111111111111111111000000", info);
    ts[49] = encrypt_input("00011111111111111111111111000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[31];
    ctxt ss[29];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    vs[2] = ts[4]; // vector load instr
    vs[3] = ts[6]; // vector load instr
    vs[4] = ts[8]; // vector load instr
    vs[5] = ts[10]; // vector load instr
    vs[6] = ts[12]; // vector load instr
    info.eval->rotate_rows(vs[6], -4, gk, ss[0]); // __s0 = __v6 >> 4
    vs[7] = ts[14]; // vector load instr
    vs[8] = ts[16]; // vector load instr
    vs[9] = ts[18]; // vector load instr
    info.eval->rotate_rows(vs[9], -8, gk, ss[1]); // __s1 = __v9 >> 8
    info.eval->rotate_rows(vs[9], -1, gk, ss[2]); // __s2 = __v9 >> 1
    
    // __t22 = blend(__v0@001000000, __s0@000100000, __t20@000010000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[0], bits["001000000"], t22_1);
    info.eval->multiply_plain(ss[0], bits["000100000"], t22_2);
    info.eval->add_many({t22_1, t22_2, ts[20]}, ts[22]);
    
    
    // __t23 = blend(__s1@001000000, __v9@000100000, __t21@000010000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(ss[1], bits["001000000"], t23_1);
    info.eval->multiply_plain(vs[9], bits["000100000"], t23_2);
    info.eval->add_many({t23_1, t23_2, ts[21]}, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[10]); // __v10 = __t22 * __t23
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -7, gk, ss[3]); // __s3 = __v10 >> 7
    info.eval->rotate_rows(vs[10], -8, gk, ss[4]); // __s4 = __v10 >> 8
    info.eval->multiply(vs[3], ss[2], vs[11]); // __v11 = __v3 * __s2
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t24 = blend(__v0@001000000, __s0@000100000, __v3@000010000)
    ctxt t24_1, t24_2, t24_3;
    info.eval->multiply_plain(vs[0], bits["001000000"], t24_1);
    info.eval->multiply_plain(ss[0], bits["000100000"], t24_2);
    info.eval->multiply_plain(vs[3], bits["000010000"], t24_3);
    info.eval->add_many({t24_1, t24_2, t24_3}, ts[24]);
    
    
    // __t25 = blend(__s3@001000000, __s4@000100000, __v10@000010000)
    ctxt t25_1, t25_2, t25_3;
    info.eval->multiply_plain(ss[3], bits["001000000"], t25_1);
    info.eval->multiply_plain(ss[4], bits["000100000"], t25_2);
    info.eval->multiply_plain(vs[10], bits["000010000"], t25_3);
    info.eval->add_many({t25_1, t25_2, t25_3}, ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[12]); // __v12 = __t24 * __t25
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -4, gk, ss[5]); // __s5 = __v12 >> 4
    vs[13] = ts[26]; // vector load instr
    info.eval->rotate_rows(vs[13], -4, gk, ss[6]); // __s6 = __v13 >> 4
    info.eval->rotate_rows(vs[13], -7, gk, ss[7]); // __s7 = __v13 >> 7
    
    // __t30 = blend(__v0@001000000, __v3@000010000, __v6@000000001, __t28@000000010)
    ctxt t30_1, t30_2, t30_3;
    info.eval->multiply_plain(vs[0], bits["001000000"], t30_1);
    info.eval->multiply_plain(vs[3], bits["000010000"], t30_2);
    info.eval->multiply_plain(vs[6], bits["000000001"], t30_3);
    info.eval->add_many({t30_1, t30_2, t30_3, ts[28]}, ts[30]);
    
    
    // __t31 = blend(__s7@001000000, __v13@000010000, __s6@000000001, __t29@000000010)
    ctxt t31_1, t31_2, t31_3;
    info.eval->multiply_plain(ss[7], bits["001000000"], t31_1);
    info.eval->multiply_plain(vs[13], bits["000010000"], t31_2);
    info.eval->multiply_plain(ss[6], bits["000000001"], t31_3);
    info.eval->add_many({t31_1, t31_2, t31_3, ts[29]}, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[14]); // __v14 = __t30 * __t31
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -8, gk, ss[8]); // __s8 = __v14 >> 8
    info.eval->rotate_rows(vs[14], -6, gk, ss[9]); // __s9 = __v14 >> 6
    
    // __t34 = blend(__v1@000010000, __v4@000000100, __t32@000000010)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[1], bits["000010000"], t34_1);
    info.eval->multiply_plain(vs[4], bits["000000100"], t34_2);
    info.eval->add_many({t34_1, t34_2, ts[32]}, ts[34]);
    
    
    // __t35 = blend(__s9@000010000, __s8@000000100, __t33@000000010)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(ss[9], bits["000010000"], t35_1);
    info.eval->multiply_plain(ss[8], bits["000000100"], t35_2);
    info.eval->add_many({t35_1, t35_2, ts[33]}, ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[15]); // __v15 = __t34 * __t35
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->rotate_rows(vs[15], -6, gk, ss[10]); // __s10 = __v15 >> 6
    info.eval->rotate_rows(vs[15], -8, gk, ss[11]); // __s11 = __v15 >> 8
    info.eval->multiply(vs[7], vs[14], vs[16]); // __v16 = __v7 * __v14
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->rotate_rows(vs[16], -6, gk, ss[12]); // __s12 = __v16 >> 6
    
    // __t38 = blend(__v4@000000100, __v7@000000010, __t36@000010000)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(vs[4], bits["000000100"], t38_1);
    info.eval->multiply_plain(vs[7], bits["000000010"], t38_2);
    info.eval->add_many({t38_1, t38_2, ts[36]}, ts[38]);
    
    
    // __t39 = blend(__s11@000000100, __v15@000000010, __t37@000010000)
    ctxt t39_1, t39_2;
    info.eval->multiply_plain(ss[11], bits["000000100"], t39_1);
    info.eval->multiply_plain(vs[15], bits["000000010"], t39_2);
    info.eval->add_many({t39_1, t39_2, ts[37]}, ts[39]);
    
    info.eval->multiply(ts[38], ts[39], vs[17]); // __v17 = __t38 * __t39
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->rotate_rows(vs[17], -2, gk, ss[13]); // __s13 = __v17 >> 2
    info.eval->rotate_rows(vs[17], -3, gk, ss[14]); // __s14 = __v17 >> 3
    info.eval->multiply(vs[1], ss[10], vs[18]); // __v18 = __v1 * __s10
    info.eval->relinearize_inplace(vs[18], rk);
    info.eval->rotate_rows(vs[18], -2, gk, ss[15]); // __s15 = __v18 >> 2
    
    // __t42 = blend(__v1@000010000, __v4@000000100, __v7@000000010, __t40@000001000)
    ctxt t42_1, t42_2, t42_3;
    info.eval->multiply_plain(vs[1], bits["000010000"], t42_1);
    info.eval->multiply_plain(vs[4], bits["000000100"], t42_2);
    info.eval->multiply_plain(vs[7], bits["000000010"], t42_3);
    info.eval->add_many({t42_1, t42_2, t42_3, ts[40]}, ts[42]);
    
    
    // __t43 = blend(__v17@000010000, __s13@000000100, __s14@000000010, __t41@000001000)
    ctxt t43_1, t43_2, t43_3;
    info.eval->multiply_plain(vs[17], bits["000010000"], t43_1);
    info.eval->multiply_plain(ss[13], bits["000000100"], t43_2);
    info.eval->multiply_plain(ss[14], bits["000000010"], t43_3);
    info.eval->add_many({t43_1, t43_2, t43_3, ts[41]}, ts[43]);
    
    info.eval->multiply(ts[42], ts[43], vs[19]); // __v19 = __t42 * __t43
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->rotate_rows(vs[19], -7, gk, ss[16]); // __s16 = __v19 >> 7
    info.eval->rotate_rows(vs[19], -6, gk, ss[17]); // __s17 = __v19 >> 6
    
    // __t44 = blend(__v2@001000000, __v5@000100000, __v8@000001000)
    ctxt t44_1, t44_2, t44_3;
    info.eval->multiply_plain(vs[2], bits["001000000"], t44_1);
    info.eval->multiply_plain(vs[5], bits["000100000"], t44_2);
    info.eval->multiply_plain(vs[8], bits["000001000"], t44_3);
    info.eval->add_many({t44_1, t44_2, t44_3}, ts[44]);
    
    
    // __t45 = blend(__s17@001000000, __s16@000100000, __v19@000001000)
    ctxt t45_1, t45_2, t45_3;
    info.eval->multiply_plain(ss[17], bits["001000000"], t45_1);
    info.eval->multiply_plain(ss[16], bits["000100000"], t45_2);
    info.eval->multiply_plain(vs[19], bits["000001000"], t45_3);
    info.eval->add_many({t45_1, t45_2, t45_3}, ts[45]);
    
    info.eval->multiply(ts[44], ts[45], vs[20]); // __v20 = __t44 * __t45
    info.eval->relinearize_inplace(vs[20], rk);
    info.eval->rotate_rows(vs[20], -8, gk, ss[18]); // __s18 = __v20 >> 8
    info.eval->rotate_rows(vs[20], -3, gk, ss[19]); // __s19 = __v20 >> 3
    vs[21] = ts[46]; // vector load instr
    info.eval->rotate_rows(vs[21], -1, gk, ss[20]); // __s20 = __v21 >> 1
    info.eval->rotate_rows(vs[21], -3, gk, ss[21]); // __s21 = __v21 >> 3
    
    // __t50 = blend(__v2@001000000, __v8@000001000, __t48@000100000)
    ctxt t50_1, t50_2;
    info.eval->multiply_plain(vs[2], bits["001000000"], t50_1);
    info.eval->multiply_plain(vs[8], bits["000001000"], t50_2);
    info.eval->add_many({t50_1, t50_2, ts[48]}, ts[50]);
    
    
    // __t51 = blend(__v21@001000000, __s21@000001000, __t49@000100000)
    ctxt t51_1, t51_2;
    info.eval->multiply_plain(vs[21], bits["001000000"], t51_1);
    info.eval->multiply_plain(ss[21], bits["000001000"], t51_2);
    info.eval->add_many({t51_1, t51_2, ts[49]}, ts[51]);
    
    info.eval->multiply(ts[50], ts[51], vs[22]); // __v22 = __t50 * __t51
    info.eval->relinearize_inplace(vs[22], rk);
    info.eval->rotate_rows(vs[22], -4, gk, ss[22]); // __s22 = __v22 >> 4
    info.eval->rotate_rows(vs[22], -8, gk, ss[23]); // __s23 = __v22 >> 8
    info.eval->rotate_rows(vs[22], -2, gk, ss[24]); // __s24 = __v22 >> 2
    info.eval->multiply(vs[5], ss[20], vs[23]); // __v23 = __v5 * __s20
    info.eval->relinearize_inplace(vs[23], rk);
    info.eval->rotate_rows(vs[23], -5, gk, ss[25]); // __s25 = __v23 >> 5
    
    // __t52 = blend(__s10@010000000, __s12@000010000, __v15@000000100)
    ctxt t52_1, t52_2, t52_3;
    info.eval->multiply_plain(ss[10], bits["010000000"], t52_1);
    info.eval->multiply_plain(ss[12], bits["000010000"], t52_2);
    info.eval->multiply_plain(vs[15], bits["000000100"], t52_3);
    info.eval->add_many({t52_1, t52_2, t52_3}, ts[52]);
    
    
    // __t53 = blend(__s18@010010000, __s19@000000100)
    ctxt t53_1, t53_2;
    info.eval->multiply_plain(ss[18], bits["010010000"], t53_1);
    info.eval->multiply_plain(ss[19], bits["000000100"], t53_2);
    info.eval->add(t53_1, t53_2, ts[53]);
    
    info.eval->add(ts[52], ts[53], vs[24]); // __v24 = __t52 + __t53
    info.eval->rotate_rows(vs[24], -8, gk, ss[26]); // __s26 = __v24 >> 8
    info.eval->rotate_rows(vs[24], -6, gk, ss[27]); // __s27 = __v24 >> 6
    info.eval->rotate_rows(vs[24], -7, gk, ss[28]); // __s28 = __v24 >> 7
    
    // __t54 = blend(__v2@001000000, __v5@000100000, __v8@000001000)
    ctxt t54_1, t54_2, t54_3;
    info.eval->multiply_plain(vs[2], bits["001000000"], t54_1);
    info.eval->multiply_plain(vs[5], bits["000100000"], t54_2);
    info.eval->multiply_plain(vs[8], bits["000001000"], t54_3);
    info.eval->add_many({t54_1, t54_2, t54_3}, ts[54]);
    
    
    // __t55 = blend(__s23@001000000, __v22@000100000, __s24@000001000)
    ctxt t55_1, t55_2, t55_3;
    info.eval->multiply_plain(ss[23], bits["001000000"], t55_1);
    info.eval->multiply_plain(vs[22], bits["000100000"], t55_2);
    info.eval->multiply_plain(ss[24], bits["000001000"], t55_3);
    info.eval->add_many({t55_1, t55_2, t55_3}, ts[55]);
    
    info.eval->multiply(ts[54], ts[55], vs[25]); // __v25 = __t54 * __t55
    info.eval->relinearize_inplace(vs[25], rk);
    
    // __t56 = blend(__s3@110000000, __v11@000010000, __s15@000000100, __v17@000000010, __s13@000000001)
    ctxt t56_1, t56_2, t56_3, t56_4, t56_5;
    info.eval->multiply_plain(ss[3], bits["110000000"], t56_1);
    info.eval->multiply_plain(vs[11], bits["000010000"], t56_2);
    info.eval->multiply_plain(ss[15], bits["000000100"], t56_3);
    info.eval->multiply_plain(vs[17], bits["000000010"], t56_4);
    info.eval->multiply_plain(ss[13], bits["000000001"], t56_5);
    info.eval->add_many({t56_1, t56_2, t56_3, t56_4, t56_5}, ts[56]);
    
    
    // __t57 = blend(__s26@100000000, __s27@010000000, __s28@000010000, __s22@000000100, __s24@000000010, __s25@000000001)
    ctxt t57_1, t57_2, t57_3, t57_4, t57_5, t57_6;
    info.eval->multiply_plain(ss[26], bits["100000000"], t57_1);
    info.eval->multiply_plain(ss[27], bits["010000000"], t57_2);
    info.eval->multiply_plain(ss[28], bits["000010000"], t57_3);
    info.eval->multiply_plain(ss[22], bits["000000100"], t57_4);
    info.eval->multiply_plain(ss[24], bits["000000010"], t57_5);
    info.eval->multiply_plain(ss[25], bits["000000001"], t57_6);
    info.eval->add_many({t57_1, t57_2, t57_3, t57_4, t57_5, t57_6}, ts[57]);
    
    info.eval->add(ts[56], ts[57], vs[26]); // __v26 = __t56 + __t57
    info.eval->add(ss[5], vs[26], vs[27]); // __v27 = __s5 + __v26
    
    // __t58 = blend(__s16@001001000, __s17@000100000, __s5@000000101)
    ctxt t58_1, t58_2, t58_3;
    info.eval->multiply_plain(ss[16], bits["001001000"], t58_1);
    info.eval->multiply_plain(ss[17], bits["000100000"], t58_2);
    info.eval->multiply_plain(ss[5], bits["000000101"], t58_3);
    info.eval->add_many({t58_1, t58_2, t58_3}, ts[58]);
    
    
    // __t59 = blend(__v25@001101000, __v26@000000101)
    ctxt t59_1, t59_2;
    info.eval->multiply_plain(vs[25], bits["001101000"], t59_1);
    info.eval->multiply_plain(vs[26], bits["000000101"], t59_2);
    info.eval->add(t59_1, t59_2, ts[59]);
    
    info.eval->add(ts[58], ts[59], vs[28]); // __v28 = __t58 + __t59
    
    // __t60 = blend(__s8@000100000, __s9@000001000)
    ctxt t60_1, t60_2;
    info.eval->multiply_plain(ss[8], bits["000100000"], t60_1);
    info.eval->multiply_plain(ss[9], bits["000001000"], t60_2);
    info.eval->add(t60_1, t60_2, ts[60]);
    
    info.eval->add(ts[60], vs[28], vs[29]); // __v29 = __t60 + __v28
    info.eval->add(vs[14], vs[28], vs[30]); // __v30 = __v14 + __v28
    return vs[30];
}
    