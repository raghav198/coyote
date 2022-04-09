
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "110000000", info);
    add_bitstring(bits, "000010100", info);
    add_bitstring(bits, "000000001", info);
    add_bitstring(bits, "000000100", info);
    add_bitstring(bits, "001000000", info);
    add_bitstring(bits, "011000000", info);
    add_bitstring(bits, "010000000", info);
    add_bitstring(bits, "000101010", info);
    add_bitstring(bits, "000000010", info);
    add_bitstring(bits, "000100000", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "001010000", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "000100010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(61);
    ts[0] = encrypt_input("00001111111111111111111001100000", info);
    ts[1] = encrypt_input("00001111111111111111111001100000", info);
    ts[2] = encrypt_input("00111111111111111111101110000000", info);
    ts[3] = encrypt_input("00111111111111111111101110000000", info);
    ts[4] = encrypt_input("00011111111111111111110111000000", info);
    ts[5] = encrypt_input("00011111111111111111110111000000", info);
    ts[6] = encrypt_input("00000000111111111111111111110110", info);
    ts[7] = encrypt_input("00000000111111111111111111110110", info);
    ts[8] = encrypt_input("00011111111111111111111111000000", info);
    ts[9] = encrypt_input("00011111111111111111111111000000", info);
    ts[10] = encrypt_input("00000001111111111111111111111100", info);
    ts[11] = encrypt_input("00000001111111111111111111111100", info);
    ts[12] = encrypt_input("00000111111111111111111110110000", info);
    ts[13] = encrypt_input("00000111111111111111111110110000", info);
    ts[14] = encrypt_input("00000001111111111111111111111100", info);
    ts[15] = encrypt_input("00000001111111111111111111111100", info);
    ts[16] = encrypt_input("00000111111111111111111111110000", info);
    ts[17] = encrypt_input("00000111111111111111111111110000", info);
    ts[18] = encrypt_input("00000111111111111111111100110000", info);
    ts[19] = encrypt_input("00000111111111111111111100110000", info);
    ts[22] = encrypt_input("00000000111111111111111111101110", info);
    ts[23] = encrypt_input("00000000111111111111111111101110", info);
    ts[24] = encrypt_input("00000000111111111111111111101110", info);
    ts[25] = encrypt_input("00000000111111111111111111101110", info);
    ts[28] = encrypt_input("00111111111111111111110110000000", info);
    ts[29] = encrypt_input("00111111111111111111110110000000", info);
    ts[32] = encrypt_input("01111111111111111111111100000000", info);
    ts[33] = encrypt_input("01111111111111111111111100000000", info);
    ts[36] = encrypt_input("00111111111111111111111110000000", info);
    ts[37] = encrypt_input("00111111111111111111111110000000", info);
    ts[40] = encrypt_input("00001111111111111111111101100000", info);
    ts[41] = encrypt_input("00001111111111111111111101100000", info);
    ts[46] = encrypt_input("00001111111111111111111111100000", info);
    ts[47] = encrypt_input("00001111111111111111111111100000", info);
    ts[48] = encrypt_input("00000001111111111111111111111100", info);
    ts[49] = encrypt_input("00000001111111111111111111111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[28];
    ctxt ss[33];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -1, gk, ss[0]); // __s0 = __v2 >> 1
    vs[3] = ts[6]; // vector load instr
    vs[4] = ts[8]; // vector load instr
    info.eval->rotate_rows(vs[4], -3, gk, ss[1]); // __s1 = __v4 >> 3
    vs[5] = ts[10]; // vector load instr
    vs[6] = ts[12]; // vector load instr
    info.eval->rotate_rows(vs[6], -1, gk, ss[2]); // __s2 = __v6 >> 1
    vs[7] = ts[14]; // vector load instr
    info.eval->rotate_rows(vs[7], -3, gk, ss[3]); // __s3 = __v7 >> 3
    info.eval->rotate_rows(vs[7], -7, gk, ss[4]); // __s4 = __v7 >> 7
    vs[8] = ts[16]; // vector load instr
    vs[9] = ts[18]; // vector load instr
    info.eval->rotate_rows(vs[9], -8, gk, ss[5]); // __s5 = __v9 >> 8
    info.eval->rotate_rows(vs[9], -3, gk, ss[6]); // __s6 = __v9 >> 3
    
    // __t20 = blend(__v0@000010000, __v6@000001000, __v3@000000001)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(vs[0], bits["000010000"], t20_1);
    info.eval->multiply_plain(vs[6], bits["000001000"], t20_2);
    info.eval->multiply_plain(vs[3], bits["000000001"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3}, ts[20]);
    
    
    // __t21 = blend(__s5@000010000, __v9@000001000, __s6@000000001)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(ss[5], bits["000010000"], t21_1);
    info.eval->multiply_plain(vs[9], bits["000001000"], t21_2);
    info.eval->multiply_plain(ss[6], bits["000000001"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3}, ts[21]);
    
    info.eval->multiply(ts[20], ts[21], vs[10]); // __v10 = __t20 * __t21
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -5, gk, ss[7]); // __s7 = __v10 >> 5
    vs[11] = ts[22]; // vector load instr
    info.eval->rotate_rows(vs[11], -5, gk, ss[8]); // __s8 = __v11 >> 5
    info.eval->rotate_rows(vs[11], -7, gk, ss[9]); // __s9 = __v11 >> 7
    
    // __t26 = blend(__v0@000010000, __s2@000000100, __t24@000000001)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(vs[0], bits["000010000"], t26_1);
    info.eval->multiply_plain(ss[2], bits["000000100"], t26_2);
    info.eval->add_many({t26_1, t26_2, ts[24]}, ts[26]);
    
    
    // __t27 = blend(__s8@000010000, __s9@000000100, __t25@000000001)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(ss[8], bits["000010000"], t27_1);
    info.eval->multiply_plain(ss[9], bits["000000100"], t27_2);
    info.eval->add_many({t27_1, t27_2, ts[25]}, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[12]); // __v12 = __t26 * __t27
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -7, gk, ss[10]); // __s10 = __v12 >> 7
    info.eval->rotate_rows(vs[12], -5, gk, ss[11]); // __s11 = __v12 >> 5
    info.eval->multiply(vs[3], vs[11], vs[13]); // __v13 = __v3 * __v11
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->rotate_rows(vs[13], -7, gk, ss[12]); // __s12 = __v13 >> 7
    
    // __t30 = blend(__v0@000010000, __s2@000000100, __v3@000000001, __t28@001000000)
    ctxt t30_1, t30_2, t30_3;
    info.eval->multiply_plain(vs[0], bits["000010000"], t30_1);
    info.eval->multiply_plain(ss[2], bits["000000100"], t30_2);
    info.eval->multiply_plain(vs[3], bits["000000001"], t30_3);
    info.eval->add_many({t30_1, t30_2, t30_3, ts[28]}, ts[30]);
    
    
    // __t31 = blend(__s11@000010000, __s10@000000100, __v12@000000001, __t29@001000000)
    ctxt t31_1, t31_2, t31_3;
    info.eval->multiply_plain(ss[11], bits["000010000"], t31_1);
    info.eval->multiply_plain(ss[10], bits["000000100"], t31_2);
    info.eval->multiply_plain(vs[12], bits["000000001"], t31_3);
    info.eval->add_many({t31_1, t31_2, t31_3, ts[29]}, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[14]); // __v14 = __t30 * __t31
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -8, gk, ss[13]); // __s13 = __v14 >> 8
    info.eval->rotate_rows(vs[14], -4, gk, ss[14]); // __s14 = __v14 >> 4
    
    // __t34 = blend(__v1@001000000, __s1@000000100, __t32@010000000)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[1], bits["001000000"], t34_1);
    info.eval->multiply_plain(ss[1], bits["000000100"], t34_2);
    info.eval->add_many({t34_1, t34_2, ts[32]}, ts[34]);
    
    
    // __t35 = blend(__v14@001000000, __s14@000000100, __t33@010000000)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[14], bits["001000000"], t35_1);
    info.eval->multiply_plain(ss[14], bits["000000100"], t35_2);
    info.eval->add_many({t35_1, t35_2, ts[33]}, ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[15]); // __v15 = __t34 * __t35
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->rotate_rows(vs[15], -1, gk, ss[15]); // __s15 = __v15 >> 1
    info.eval->rotate_rows(vs[15], -2, gk, ss[16]); // __s16 = __v15 >> 2
    info.eval->rotate_rows(vs[15], -8, gk, ss[17]); // __s17 = __v15 >> 8
    info.eval->multiply(ss[3], ss[13], vs[16]); // __v16 = __s3 * __s13
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->rotate_rows(vs[16], -1, gk, ss[18]); // __s18 = __v16 >> 1
    
    // __t38 = blend(__s3@010000000, __v4@000100000, __t36@001000000)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(ss[3], bits["010000000"], t38_1);
    info.eval->multiply_plain(vs[4], bits["000100000"], t38_2);
    info.eval->add_many({t38_1, t38_2, ts[36]}, ts[38]);
    
    
    // __t39 = blend(__v15@010000000, __s16@000100000, __t37@001000000)
    ctxt t39_1, t39_2;
    info.eval->multiply_plain(vs[15], bits["010000000"], t39_1);
    info.eval->multiply_plain(ss[16], bits["000100000"], t39_2);
    info.eval->add_many({t39_1, t39_2, ts[37]}, ts[39]);
    
    info.eval->multiply(ts[38], ts[39], vs[17]); // __v17 = __t38 * __t39
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->rotate_rows(vs[17], -3, gk, ss[19]); // __s19 = __v17 >> 3
    info.eval->rotate_rows(vs[17], -4, gk, ss[20]); // __s20 = __v17 >> 4
    info.eval->multiply(vs[1], ss[15], vs[18]); // __v18 = __v1 * __s15
    info.eval->relinearize_inplace(vs[18], rk);
    
    // __t42 = blend(__v1@001000000, __s4@000001000, __s1@000000100, __t40@000010000)
    ctxt t42_1, t42_2, t42_3;
    info.eval->multiply_plain(vs[1], bits["001000000"], t42_1);
    info.eval->multiply_plain(ss[4], bits["000001000"], t42_2);
    info.eval->multiply_plain(ss[1], bits["000000100"], t42_3);
    info.eval->add_many({t42_1, t42_2, t42_3, ts[40]}, ts[42]);
    
    
    // __t43 = blend(__v17@001000000, __s19@000001000, __s20@000000100, __t41@000010000)
    ctxt t43_1, t43_2, t43_3;
    info.eval->multiply_plain(vs[17], bits["001000000"], t43_1);
    info.eval->multiply_plain(ss[19], bits["000001000"], t43_2);
    info.eval->multiply_plain(ss[20], bits["000000100"], t43_3);
    info.eval->add_many({t43_1, t43_2, t43_3, ts[41]}, ts[43]);
    
    info.eval->multiply(ts[42], ts[43], vs[19]); // __v19 = __t42 * __t43
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->rotate_rows(vs[19], -1, gk, ss[21]); // __s21 = __v19 >> 1
    info.eval->rotate_rows(vs[19], -3, gk, ss[22]); // __s22 = __v19 >> 3
    
    // __t44 = blend(__s0@000010000, __v8@000001000, __v5@000000010)
    ctxt t44_1, t44_2, t44_3;
    info.eval->multiply_plain(ss[0], bits["000010000"], t44_1);
    info.eval->multiply_plain(vs[8], bits["000001000"], t44_2);
    info.eval->multiply_plain(vs[5], bits["000000010"], t44_3);
    info.eval->add_many({t44_1, t44_2, t44_3}, ts[44]);
    
    
    // __t45 = blend(__v19@000010000, __s21@000001000, __s22@000000010)
    ctxt t45_1, t45_2, t45_3;
    info.eval->multiply_plain(vs[19], bits["000010000"], t45_1);
    info.eval->multiply_plain(ss[21], bits["000001000"], t45_2);
    info.eval->multiply_plain(ss[22], bits["000000010"], t45_3);
    info.eval->add_many({t45_1, t45_2, t45_3}, ts[45]);
    
    info.eval->multiply(ts[44], ts[45], vs[20]); // __v20 = __t44 * __t45
    info.eval->relinearize_inplace(vs[20], rk);
    info.eval->rotate_rows(vs[20], -6, gk, ss[23]); // __s23 = __v20 >> 6
    info.eval->rotate_rows(vs[20], -1, gk, ss[24]); // __s24 = __v20 >> 1
    vs[21] = ts[46]; // vector load instr
    info.eval->rotate_rows(vs[21], -1, gk, ss[25]); // __s25 = __v21 >> 1
    info.eval->rotate_rows(vs[21], -3, gk, ss[26]); // __s26 = __v21 >> 3
    
    // __t50 = blend(__v8@000001000, __t48@000000010)
    ctxt t50_1;
    info.eval->multiply_plain(vs[8], bits["000001000"], t50_1);
    info.eval->add(t50_1, ts[48], ts[50]);
    
    
    // __t51 = blend(__s25@000001000, __t49@000000010)
    ctxt t51_1;
    info.eval->multiply_plain(ss[25], bits["000001000"], t51_1);
    info.eval->add(t51_1, ts[49], ts[51]);
    
    info.eval->multiply(ts[50], ts[51], vs[22]); // __v22 = __t50 * __t51
    info.eval->relinearize_inplace(vs[22], rk);
    info.eval->rotate_rows(vs[22], -8, gk, ss[27]); // __s27 = __v22 >> 8
    info.eval->rotate_rows(vs[22], -5, gk, ss[28]); // __s28 = __v22 >> 5
    info.eval->rotate_rows(vs[22], -7, gk, ss[29]); // __s29 = __v22 >> 7
    
    // __t52 = blend(__s17@010000000, __s18@001000000, __s16@000000001)
    ctxt t52_1, t52_2, t52_3;
    info.eval->multiply_plain(ss[17], bits["010000000"], t52_1);
    info.eval->multiply_plain(ss[18], bits["001000000"], t52_2);
    info.eval->multiply_plain(ss[16], bits["000000001"], t52_3);
    info.eval->add_many({t52_1, t52_2, t52_3}, ts[52]);
    
    
    // __t53 = blend(__s23@011000000, __s24@000000001)
    ctxt t53_1, t53_2;
    info.eval->multiply_plain(ss[23], bits["011000000"], t53_1);
    info.eval->multiply_plain(ss[24], bits["000000001"], t53_2);
    info.eval->add(t53_1, t53_2, ts[53]);
    
    info.eval->add(ts[52], ts[53], vs[23]); // __v23 = __t52 + __t53
    info.eval->rotate_rows(vs[23], -8, gk, ss[30]); // __s30 = __v23 >> 8
    
    // __t54 = blend(__s0@000010000, __v5@000000010)
    ctxt t54_1, t54_2;
    info.eval->multiply_plain(ss[0], bits["000010000"], t54_1);
    info.eval->multiply_plain(vs[5], bits["000000010"], t54_2);
    info.eval->add(t54_1, t54_2, ts[54]);
    
    
    // __t55 = blend(__v21@000010000, __s26@000000010)
    ctxt t55_1, t55_2;
    info.eval->multiply_plain(vs[21], bits["000010000"], t55_1);
    info.eval->multiply_plain(ss[26], bits["000000010"], t55_2);
    info.eval->add(t55_1, t55_2, ts[55]);
    
    info.eval->multiply(ts[54], ts[55], vs[24]); // __v24 = __t54 * __t55
    info.eval->relinearize_inplace(vs[24], rk);
    info.eval->rotate_rows(vs[24], -7, gk, ss[31]); // __s31 = __v24 >> 7
    info.eval->rotate_rows(vs[24], -8, gk, ss[32]); // __s32 = __v24 >> 8
    
    // __t56 = blend(__v2@000100000, __v8@000001000, __v5@000000010)
    ctxt t56_1, t56_2, t56_3;
    info.eval->multiply_plain(vs[2], bits["000100000"], t56_1);
    info.eval->multiply_plain(vs[8], bits["000001000"], t56_2);
    info.eval->multiply_plain(vs[5], bits["000000010"], t56_3);
    info.eval->add_many({t56_1, t56_2, t56_3}, ts[56]);
    
    
    // __t57 = blend(__s28@000100000, __s29@000001000, __v22@000000010)
    ctxt t57_1, t57_2, t57_3;
    info.eval->multiply_plain(ss[28], bits["000100000"], t57_1);
    info.eval->multiply_plain(ss[29], bits["000001000"], t57_2);
    info.eval->multiply_plain(vs[22], bits["000000010"], t57_3);
    info.eval->add_many({t57_1, t57_2, t57_3}, ts[57]);
    
    info.eval->multiply(ts[56], ts[57], vs[25]); // __v25 = __t56 * __t57
    info.eval->relinearize_inplace(vs[25], rk);
    
    // __t58 = blend(__s7@110000000, __v18@001000000, __s21@000100010, __s19@000010100, __v19@000001000, __v10@000000001)
    ctxt t58_1, t58_2, t58_3, t58_4, t58_5, t58_6;
    info.eval->multiply_plain(ss[7], bits["110000000"], t58_1);
    info.eval->multiply_plain(vs[18], bits["001000000"], t58_2);
    info.eval->multiply_plain(ss[21], bits["000100010"], t58_3);
    info.eval->multiply_plain(ss[19], bits["000010100"], t58_4);
    info.eval->multiply_plain(vs[19], bits["000001000"], t58_5);
    info.eval->multiply_plain(vs[10], bits["000000001"], t58_6);
    info.eval->add_many({t58_1, t58_2, t58_3, t58_4, t58_5, t58_6}, ts[58]);
    
    
    // __t59 = blend(__s30@110000000, __s31@001000000, __v25@000101010, __s27@000010000, __s32@000000100, __v23@000000001)
    ctxt t59_1, t59_2, t59_3, t59_4, t59_5, t59_6;
    info.eval->multiply_plain(ss[30], bits["110000000"], t59_1);
    info.eval->multiply_plain(ss[31], bits["001000000"], t59_2);
    info.eval->multiply_plain(vs[25], bits["000101010"], t59_3);
    info.eval->multiply_plain(ss[27], bits["000010000"], t59_4);
    info.eval->multiply_plain(ss[32], bits["000000100"], t59_5);
    info.eval->multiply_plain(vs[23], bits["000000001"], t59_6);
    info.eval->add_many({t59_1, t59_2, t59_3, t59_4, t59_5, t59_6}, ts[59]);
    
    info.eval->add(ts[58], ts[59], vs[26]); // __v26 = __t58 + __t59
    
    // __t60 = blend(__s10@001010000, __s13@000101010, __s12@000000100)
    ctxt t60_1, t60_2, t60_3;
    info.eval->multiply_plain(ss[10], bits["001010000"], t60_1);
    info.eval->multiply_plain(ss[13], bits["000101010"], t60_2);
    info.eval->multiply_plain(ss[12], bits["000000100"], t60_3);
    info.eval->add_many({t60_1, t60_2, t60_3}, ts[60]);
    
    info.eval->add(ts[60], vs[26], vs[27]); // __v27 = __t60 + __v26
    return vs[27];
}
    