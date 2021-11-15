
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100000000000100100000000", info);
    add_bitstring(bits, "000100000000000100000000", info);
    add_bitstring(bits, "100000000000000000000000", info);
    add_bitstring(bits, "100000000000000100000000", info);
    add_bitstring(bits, "000000000000100000000000", info);
    add_bitstring(bits, "000100000000000000000000", info);
    add_bitstring(bits, "000000000000000100000000", info);
    add_bitstring(bits, "100100000000000000000000", info);
    add_bitstring(bits, "100000000000100000000000", info);
    add_bitstring(bits, "000100000000100000000000", info);
    add_bitstring(bits, "000000000000100100000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(60);
    ts[0] = encrypt_input("00011011110110000011011111110111110011010000111110011110", info);
    ts[2] = encrypt_input("111101101011111110111111111110111111101111011110111101011111111101101011111111101101011111111111101111011111111101111011", info);
    ts[4] = encrypt_input("1111000000000000000000000000", info);
    ts[7] = encrypt_input("0000000000000001111100000000", info);
    ts[8] = encrypt_input("00000000000011111001111100000000", info);
    ts[11] = encrypt_input("0000000000001111000000000000", info);
    ts[12] = encrypt_input("0000000000001111100000000000", info);
    ts[15] = encrypt_input("11110001111000000000000000000000", info);
    ts[16] = encrypt_input("11110001111100000000000000000000", info);
    ts[19] = encrypt_input("1111100000000000000000000000", info);
    ts[20] = encrypt_input("1111100000000000000000000000", info);
    ts[23] = encrypt_input("00000000000011111001111100000000", info);
    ts[24] = encrypt_input("00000000000011111001111100000000", info);
    ts[27] = encrypt_input("1111100000000000000000000000", info);
    ts[28] = encrypt_input("11111000000000001111100000000000", info);
    ts[31] = encrypt_input("00011111000000001111100000000000", info);
    ts[32] = encrypt_input("111110011111000000001111100000000000", info);
    ts[35] = encrypt_input("0000000000000001111000000000", info);
    ts[36] = encrypt_input("0000000000000001111000000000", info);
    ts[42] = encrypt_input("0001111100000000000000000000", info);
    ts[43] = encrypt_input("111110011111000000001111100000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[25];
    ctxt ss[17];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -12, gk, ss[0]); // __s0 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -23, gk, ss[1]); // __s1 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -17, gk, ss[2]); // __s2 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -5, gk, ss[3]); // __s3 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -16, gk, ss[4]); // __s4 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -1, gk, ss[5]); // __s5 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[6]); // __s6 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -11, gk, ss[7]); // __s7 = __v0 >> 11
    info.eval->rotate_rows(vs[0], -14, gk, ss[8]); // __s8 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -19, gk, ss[9]); // __s9 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -4, gk, ss[10]); // __s10 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -7, gk, ss[11]); // __s11 = __v0 >> 7
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -23, gk, ss[12]); // __s12 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -22, gk, ss[13]); // __s13 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -18, gk, ss[14]); // __s14 = __v1 >> 18
    info.eval->rotate_rows(vs[1], -17, gk, ss[15]); // __s15 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -16, gk, ss[16]); // __s16 = __v1 >> 16
    
    // __t5 = blend(__v1@100000000000000000000000, __s13@000100000000000000000000, __s15@000000000000100000000000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(vs[1], bits["100000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[13], bits["000100000000000000000000"], t5_2);
    info.eval->multiply_plain(ss[15], bits["000000000000100000000000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    
    // __t6 = blend(__s8@000100000000000000000000, __s5@000000000000100000000000, __t4@100000000000000000000000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[8], bits["000100000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[5], bits["000000000000100000000000"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    info.eval->multiply(ts[5], ts[6], vs[2]); // __v2 = __t5 * __t6
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t9 = blend(__s16@100000000000000000000000, __v1@000100000000000000000000, __s13@000000000000100000000000, __t7@000000000000000100000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[16], bits["100000000000000000000000"], t9_1);
    info.eval->multiply_plain(vs[1], bits["000100000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[13], bits["000000000000100000000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3, ts[7]}, ts[9]);
    
    
    // __t10 = blend(__s7@100000000000000000000000, __v0@000100000000000000000000, __t8@000000000000100100000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[7], bits["100000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[0], bits["000100000000000000000000"], t10_2);
    info.eval->add_many({t10_1, t10_2, ts[8]}, ts[10]);
    
    info.eval->multiply(ts[9], ts[00], vs[3]); // __v3 = __t9 * __t00
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t13 = blend(__s14@000100000000000000000000, __s13@000000000000000100000000, __t01@000000000000100000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[14], bits["000100000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[13], bits["000000000000000100000000"], t13_2);
    info.eval->add_many({t13_1, t13_2, ts[01]}, ts[13]);
    
    
    // __t14 = blend(__s1@000100000000000000000000, __s9@000000000000000100000000, __t02@000000000000100000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[1], bits["000100000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[9], bits["000000000000000100000000"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[02]}, ts[14]);
    
    info.eval->multiply(ts[03], ts[04], vs[4]); // __v4 = __t03 * __t04
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t17 = blend(__s16@000000000000100000000000, __s12@000000000000000100000000, __t05@100100000000000000000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[16], bits["000000000000100000000000"], t17_1);
    info.eval->multiply_plain(ss[12], bits["000000000000000100000000"], t17_2);
    info.eval->add_many({t17_1, t17_2, ts[05]}, ts[17]);
    
    
    // __t18 = blend(__s4@000000000000100000000000, __s1@000000000000000100000000, __t06@100100000000000000000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[4], bits["000000000000100000000000"], t18_1);
    info.eval->multiply_plain(ss[1], bits["000000000000000100000000"], t18_2);
    info.eval->add_many({t18_1, t18_2, ts[06]}, ts[18]);
    
    info.eval->multiply(ts[07], ts[08], vs[5]); // __v5 = __t07 * __t08
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t21 = blend(__s15@000100000000000100000000, __t09@100000000000000000000000)
    ctxt t21_1;
    info.eval->multiply_plain(ss[15], bits["000100000000000100000000"], t21_1);
    info.eval->add(t21_1, ts[09], ts[21]);
    
    
    // __t22 = blend(__s2@000100000000000000000000, __s0@000000000000000100000000, __t20@100000000000000000000000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(ss[2], bits["000100000000000000000000"], t22_1);
    info.eval->multiply_plain(ss[0], bits["000000000000000100000000"], t22_2);
    info.eval->add_many({t22_1, t22_2, ts[20]}, ts[22]);
    
    info.eval->multiply(ts[21], ts[22], vs[6]); // __v6 = __t21 * __t22
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[6], vs[3], vs[7]); // __v7 = __v6 + __v3
    
    // __t25 = blend(__s12@100000000000000000000000, __t23@000000000000100100000000)
    ctxt t25_1;
    info.eval->multiply_plain(ss[12], bits["100000000000000000000000"], t25_1);
    info.eval->add(t25_1, ts[23], ts[25]);
    
    
    // __t26 = blend(__s5@100000000000000000000000, __t24@000000000000100100000000)
    ctxt t26_1;
    info.eval->multiply_plain(ss[5], bits["100000000000000000000000"], t26_1);
    info.eval->add(t26_1, ts[24], ts[26]);
    
    info.eval->multiply(ts[25], ts[26], vs[8]); // __v8 = __t25 * __t26
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t29 = blend(__s16@000100000000000100000000, __s14@000000000000100000000000, __t27@100000000000000000000000)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(ss[16], bits["000100000000000100000000"], t29_1);
    info.eval->multiply_plain(ss[14], bits["000000000000100000000000"], t29_2);
    info.eval->add_many({t29_1, t29_2, ts[27]}, ts[29]);
    
    
    // __t30 = blend(__s4@000100000000000000000000, __s3@000000000000000100000000, __t28@100000000000100000000000)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(ss[4], bits["000100000000000000000000"], t30_1);
    info.eval->multiply_plain(ss[3], bits["000000000000000100000000"], t30_2);
    info.eval->add_many({t30_1, t30_2, ts[28]}, ts[30]);
    
    info.eval->multiply(ts[29], ts[20], vs[9]); // __v9 = __t29 * __t20
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->add(vs[7], vs[4], vs[10]); // __v10 = __v7 + __v4
    
    // __t33 = blend(__s13@100000000000000000000000, __v1@000000000000000100000000, __t21@000100000000100000000000)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(ss[13], bits["100000000000000000000000"], t33_1);
    info.eval->multiply_plain(vs[1], bits["000000000000000100000000"], t33_2);
    info.eval->add_many({t33_1, t33_2, ts[21]}, ts[33]);
    
    
    // __t34 = blend(__s4@000000000000000100000000, __t22@100100000000100000000000)
    ctxt t34_1;
    info.eval->multiply_plain(ss[4], bits["000000000000000100000000"], t34_1);
    info.eval->add(t34_1, ts[22], ts[34]);
    
    info.eval->multiply(ts[23], ts[24], vs[11]); // __v11 = __t23 * __t24
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t37 = blend(__s15@100000000000000000000000, __s12@000100000000100000000000, __t25@000000000000000100000000)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(ss[15], bits["100000000000000000000000"], t37_1);
    info.eval->multiply_plain(ss[12], bits["000100000000100000000000"], t37_2);
    info.eval->add_many({t37_1, t37_2, ts[25]}, ts[37]);
    
    
    // __t38 = blend(__s10@100000000000000000000000, __s11@000100000000000000000000, __s1@000000000000100000000000, __t26@000000000000000100000000)
    ctxt t38_1, t38_2, t38_3;
    info.eval->multiply_plain(ss[10], bits["100000000000000000000000"], t38_1);
    info.eval->multiply_plain(ss[11], bits["000100000000000000000000"], t38_2);
    info.eval->multiply_plain(ss[1], bits["000000000000100000000000"], t38_3);
    info.eval->add_many({t38_1, t38_2, t38_3, ts[26]}, ts[38]);
    
    info.eval->multiply(ts[27], ts[28], vs[12]); // __v12 = __t27 * __t28
    info.eval->relinearize_inplace(vs[12], rk);
    
    // __t39 = blend(__v10@000100000000000000000000, __v12@000000000000100000000000)
    ctxt t39_1, t39_2;
    info.eval->multiply_plain(vs[10], bits["000100000000000000000000"], t39_1);
    info.eval->multiply_plain(vs[12], bits["000000000000100000000000"], t39_2);
    info.eval->add(t39_1, t39_2, ts[39]);
    
    
    // __t40 = blend(__v2@000100000000000000000000, __v5@000000000000100000000000)
    ctxt t40_1, t40_2;
    info.eval->multiply_plain(vs[2], bits["000100000000000000000000"], t40_1);
    info.eval->multiply_plain(vs[5], bits["000000000000100000000000"], t40_2);
    info.eval->add(t40_1, t40_2, ts[40]);
    
    info.eval->add(ts[29], ts[40], vs[13]); // __v13 = __t29 + __t40
    
    // __t41 = blend(__v12@000100000000000000000000, __v2@000000000000100000000000)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(vs[12], bits["000100000000000000000000"], t41_1);
    info.eval->multiply_plain(vs[2], bits["000000000000100000000000"], t41_2);
    info.eval->add(t41_1, t41_2, ts[41]);
    
    info.eval->add(vs[13], ts[41], vs[14]); // __v14 = __v13 + __t41
    
    // __t44 = blend(__s14@100000000000000100000000, __v1@000000000000100000000000, __t42@000100000000000000000000)
    ctxt t44_1, t44_2;
    info.eval->multiply_plain(ss[14], bits["100000000000000100000000"], t44_1);
    info.eval->multiply_plain(vs[1], bits["000000000000100000000000"], t44_2);
    info.eval->add_many({t44_1, t44_2, ts[42]}, ts[44]);
    
    
    // __t45 = blend(__s6@000000000000000100000000, __t43@100100000000100000000000)
    ctxt t45_1;
    info.eval->multiply_plain(ss[6], bits["000000000000000100000000"], t45_1);
    info.eval->add(t45_1, ts[43], ts[45]);
    
    info.eval->multiply(ts[44], ts[45], vs[15]); // __v15 = __t44 * __t45
    info.eval->relinearize_inplace(vs[15], rk);
    
    // __t46 = blend(__v8@100000000000000000000000, __v14@000100000000100000000000)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(vs[8], bits["100000000000000000000000"], t46_1);
    info.eval->multiply_plain(vs[14], bits["000100000000100000000000"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    
    // __t47 = blend(__v3@100000000000000000000000, __v9@000100000000000000000000, __v15@000000000000100000000000)
    ctxt t47_1, t47_2, t47_3;
    info.eval->multiply_plain(vs[3], bits["100000000000000000000000"], t47_1);
    info.eval->multiply_plain(vs[9], bits["000100000000000000000000"], t47_2);
    info.eval->multiply_plain(vs[15], bits["000000000000100000000000"], t47_3);
    info.eval->add_many({t47_1, t47_2, t47_3}, ts[47]);
    
    info.eval->add(ts[46], ts[47], vs[16]); // __v16 = __t46 + __t47
    
    // __t48 = blend(__v16@100000000000100000000000, __v5@000000000000000100000000)
    ctxt t48_1, t48_2;
    info.eval->multiply_plain(vs[16], bits["100000000000100000000000"], t48_1);
    info.eval->multiply_plain(vs[5], bits["000000000000000100000000"], t48_2);
    info.eval->add(t48_1, t48_2, ts[48]);
    
    
    // __t49 = blend(__v12@100000000000000000000000, __v9@000000000000100100000000)
    ctxt t49_1, t49_2;
    info.eval->multiply_plain(vs[12], bits["100000000000000000000000"], t49_1);
    info.eval->multiply_plain(vs[9], bits["000000000000100100000000"], t49_2);
    info.eval->add(t49_1, t49_2, ts[49]);
    
    info.eval->add(ts[48], ts[49], vs[17]); // __v17 = __t48 + __t49
    
    // __t50 = blend(__v17@100000000000100100000000, __v16@000100000000000000000000)
    ctxt t50_1, t50_2;
    info.eval->multiply_plain(vs[17], bits["100000000000100100000000"], t50_1);
    info.eval->multiply_plain(vs[16], bits["000100000000000000000000"], t50_2);
    info.eval->add(t50_1, t50_2, ts[50]);
    
    
    // __t51 = blend(__v2@100000000000000000000000, __v5@000100000000000000000000, __v3@000000000000100000000000, __v6@000000000000000100000000)
    ctxt t51_1, t51_2, t51_3, t51_4;
    info.eval->multiply_plain(vs[2], bits["100000000000000000000000"], t51_1);
    info.eval->multiply_plain(vs[5], bits["000100000000000000000000"], t51_2);
    info.eval->multiply_plain(vs[3], bits["000000000000100000000000"], t51_3);
    info.eval->multiply_plain(vs[6], bits["000000000000000100000000"], t51_4);
    info.eval->add_many({t51_1, t51_2, t51_3, t51_4}, ts[51]);
    
    info.eval->add(ts[50], ts[51], vs[18]); // __v18 = __t50 + __t51
    
    // __t52 = blend(__v15@100100000000000000000000, __v11@000000000000000100000000)
    ctxt t52_1, t52_2;
    info.eval->multiply_plain(vs[15], bits["100100000000000000000000"], t52_1);
    info.eval->multiply_plain(vs[11], bits["000000000000000100000000"], t52_2);
    info.eval->add(t52_1, t52_2, ts[52]);
    
    info.eval->add(vs[18], ts[52], vs[19]); // __v19 = __v18 + __t52
    
    // __t53 = blend(__v11@100100000000000000000000, __v15@000000000000000100000000)
    ctxt t53_1, t53_2;
    info.eval->multiply_plain(vs[11], bits["100100000000000000000000"], t53_1);
    info.eval->multiply_plain(vs[15], bits["000000000000000100000000"], t53_2);
    info.eval->add(t53_1, t53_2, ts[53]);
    
    info.eval->add(vs[19], ts[53], vs[20]); // __v20 = __v19 + __t53
    
    // __t54 = blend(__v20@100000000000000100000000, __v18@000000000000100000000000)
    ctxt t54_1, t54_2;
    info.eval->multiply_plain(vs[20], bits["100000000000000100000000"], t54_1);
    info.eval->multiply_plain(vs[18], bits["000000000000100000000000"], t54_2);
    info.eval->add(t54_1, t54_2, ts[54]);
    
    
    // __t55 = blend(__v5@100000000000000000000000, __v4@000000000000100100000000)
    ctxt t55_1, t55_2;
    info.eval->multiply_plain(vs[5], bits["100000000000000000000000"], t55_1);
    info.eval->multiply_plain(vs[4], bits["000000000000100100000000"], t55_2);
    info.eval->add(t55_1, t55_2, ts[55]);
    
    info.eval->add(ts[54], ts[55], vs[21]); // __v21 = __t54 + __t55
    
    // __t56 = blend(__v6@100000000000000000000000, __v12@000000000000000100000000)
    ctxt t56_1, t56_2;
    info.eval->multiply_plain(vs[6], bits["100000000000000000000000"], t56_1);
    info.eval->multiply_plain(vs[12], bits["000000000000000100000000"], t56_2);
    info.eval->add(t56_1, t56_2, ts[56]);
    
    info.eval->add(vs[21], ts[56], vs[22]); // __v22 = __v21 + __t56
    
    // __t57 = blend(__v22@100000000000000100000000, __v21@000000000000100000000000)
    ctxt t57_1, t57_2;
    info.eval->multiply_plain(vs[22], bits["100000000000000100000000"], t57_1);
    info.eval->multiply_plain(vs[21], bits["000000000000100000000000"], t57_2);
    info.eval->add(t57_1, t57_2, ts[57]);
    
    
    // __t58 = blend(__v9@100000000000000000000000, __v8@000000000000100100000000)
    ctxt t58_1, t58_2;
    info.eval->multiply_plain(vs[9], bits["100000000000000000000000"], t58_1);
    info.eval->multiply_plain(vs[8], bits["000000000000100100000000"], t58_2);
    info.eval->add(t58_1, t58_2, ts[58]);
    
    info.eval->add(ts[57], ts[58], vs[23]); // __v23 = __t57 + __t58
    
    // __t59 = blend(__v11@000000000000100000000000, __v3@000000000000000100000000)
    ctxt t59_1, t59_2;
    info.eval->multiply_plain(vs[11], bits["000000000000100000000000"], t59_1);
    info.eval->multiply_plain(vs[3], bits["000000000000000100000000"], t59_2);
    info.eval->add(t59_1, t59_2, ts[59]);
    
    info.eval->add(vs[23], ts[59], vs[24]); // __v24 = __v23 + __t59
    return vs[24];
}
    