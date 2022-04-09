
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000001000000000000000", info);
    add_bitstring(bits, "00000000000100000000000000", info);
    add_bitstring(bits, "00000000000010000000000000", info);
    add_bitstring(bits, "00000000000000000000001000", info);
    add_bitstring(bits, "00000001000000000000001000", info);
    add_bitstring(bits, "00001000000000000000000000", info);
    add_bitstring(bits, "00000000000001000000000000", info);
    add_bitstring(bits, "00000000000000001000000000", info);
    add_bitstring(bits, "00000000000000000100000000", info);
    add_bitstring(bits, "00000001000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000100", info);
    add_bitstring(bits, "00000000000000000000000010", info);
    add_bitstring(bits, "00000000000000000100000010", info);
    add_bitstring(bits, "00000000000000000000010000", info);
    add_bitstring(bits, "00000000000000100000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(44);
    ts[0] = encrypt_input("0110000000000001100011100011111000", info);
    ts[1] = encrypt_input("010100000000000011000111000111111000", info);
    ts[2] = encrypt_input("1110111011100111000000011011111100000000", info);
    ts[3] = encrypt_input("1100101011100111000000011110011100000000", info);
    ts[4] = encrypt_input("00011101011101101100011100000011100000111", info);
    ts[5] = encrypt_input("00011101111110111000101100000011100000111", info);
    ts[8] = encrypt_input("0000000000011100000000000000", info);
    ts[9] = encrypt_input("0000000000011100000000000000", info);
    ts[10] = encrypt_input("0000111001110000011100000000111000", info);
    ts[11] = encrypt_input("000011100110000011100000000111000", info);
    ts[14] = encrypt_input("00001110000001110000000000011100", info);
    ts[15] = encrypt_input("00001010000001010000000000011000", info);
    ts[20] = encrypt_input("000011100000011000000000000000", info);
    ts[21] = encrypt_input("000011100000011100000000000000", info);
    ts[24] = encrypt_input("000000000011100011000000000000", info);
    ts[25] = encrypt_input("000000000011100011000000000000", info);
    ts[32] = encrypt_input("0000000000000000000000001110", info);
    ts[33] = encrypt_input("000000000000000000000000110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[21];
    ctxt ss[19];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -9, gk, ss[0]); // __s0 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -22, gk, ss[1]); // __s1 = __v0 >> 22
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -4, gk, ss[2]); // __s2 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -9, gk, ss[3]); // __s3 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -22, gk, ss[4]); // __s4 = __v1 >> 22
    
    // __t6 = blend(__v1@00000000000000000100000000, __t4@00010110100010000001000001)
    ctxt t6_1;
    info.eval->multiply_plain(vs[1], bits["00000000000000000100000000"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@00000000000000000100000000, __t5@00010110100010000001000001)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["00000000000000000100000000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -9, gk, ss[5]); // __s5 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -4, gk, ss[6]); // __s6 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -22, gk, ss[7]); // __s7 = __v2 >> 22
    info.eval->add(ts[8], ts[9], vs[3]); // __v3 = __t8 + __t9
    
    // __t12 = blend(__s5@00000000000010000000000000, __t10@00001001000001000000001000)
    ctxt t12_1;
    info.eval->multiply_plain(ss[5], bits["00000000000010000000000000"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    
    // __t13 = blend(__s4@00000000000010000000000000, __t11@00001001000001000000001000)
    ctxt t13_1;
    info.eval->multiply_plain(ss[4], bits["00000000000010000000000000"], t13_1);
    info.eval->add(t13_1, ts[11], ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[4]); // __v4 = __t12 * __t13
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -10, gk, ss[8]); // __s8 = __v4 >> 10
    
    // __t16 = blend(__v4@00000000000001000000000000, __t14@00001000000100000000000100)
    ctxt t16_1;
    info.eval->multiply_plain(vs[4], bits["00000000000001000000000000"], t16_1);
    info.eval->add(t16_1, ts[14], ts[16]);
    
    
    // __t17 = blend(__s3@00000000000001000000000000, __t15@00001000000100000000000100)
    ctxt t17_1;
    info.eval->multiply_plain(ss[3], bits["00000000000001000000000000"], t17_1);
    info.eval->add(t17_1, ts[15], ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[5]); // __v5 = __t16 + __t17
    info.eval->rotate_rows(vs[5], -10, gk, ss[9]); // __s9 = __v5 >> 10
    
    // __t18 = blend(__v4@00001000000000000000000000, __v1@00000001000000000000000000, __v0@00000000000000000000001000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[4], bits["00001000000000000000000000"], t18_1);
    info.eval->multiply_plain(vs[1], bits["00000001000000000000000000"], t18_2);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000001000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    
    // __t19 = blend(__v5@00001000000000000000000000, __v4@00000001000000000000001000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[5], bits["00001000000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[4], bits["00000001000000000000001000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[6]); // __v6 = __t18 * __t19
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -10, gk, ss[10]); // __s10 = __v6 >> 10
    
    // __t22 = blend(__v5@00000000000000000000000100, __t20@00001000000100000000000000)
    ctxt t22_1;
    info.eval->multiply_plain(vs[5], bits["00000000000000000000000100"], t22_1);
    info.eval->add(t22_1, ts[20], ts[22]);
    
    
    // __t23 = blend(__s6@00000000000000000000000100, __t21@00001000000100000000000000)
    ctxt t23_1;
    info.eval->multiply_plain(ss[6], bits["00000000000000000000000100"], t23_1);
    info.eval->add(t23_1, ts[21], ts[23]);
    
    info.eval->add(ts[22], ts[23], vs[7]); // __v7 = __t22 + __t23
    
    // __t26 = blend(__v7@00001000000000000000000000, __v5@00000000000100000000000000, __t24@00000000001000100000000000)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(vs[7], bits["00001000000000000000000000"], t26_1);
    info.eval->multiply_plain(vs[5], bits["00000000000100000000000000"], t26_2);
    info.eval->add_many({t26_1, t26_2, ts[24]}, ts[26]);
    
    
    // __t27 = blend(__s2@00001000000000000000000000, __v7@00000000000100000000000000, __t25@00000000001000100000000000)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(ss[2], bits["00001000000000000000000000"], t27_1);
    info.eval->multiply_plain(vs[7], bits["00000000000100000000000000"], t27_2);
    info.eval->add_many({t27_1, t27_2, ts[25]}, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[8]); // __v8 = __t26 * __t27
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t28 = blend(__v8@00001000000000000000000000, __s1@00000000001000000000000000, __v3@00000000000100000000000000)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[8], bits["00001000000000000000000000"], t28_1);
    info.eval->multiply_plain(ss[1], bits["00000000001000000000000000"], t28_2);
    info.eval->multiply_plain(vs[3], bits["00000000000100000000000000"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3}, ts[28]);
    
    
    // __t29 = blend(__v6@00001000000000000000000000, __v8@00000000001000000000000000, __s3@00000000000100000000000000)
    ctxt t29_1, t29_2, t29_3;
    info.eval->multiply_plain(vs[6], bits["00001000000000000000000000"], t29_1);
    info.eval->multiply_plain(vs[8], bits["00000000001000000000000000"], t29_2);
    info.eval->multiply_plain(ss[3], bits["00000000000100000000000000"], t29_3);
    info.eval->add_many({t29_1, t29_2, t29_3}, ts[29]);
    
    info.eval->add(ts[28], ts[29], vs[9]); // __v9 = __t28 + __t29
    info.eval->rotate_rows(vs[9], -10, gk, ss[11]); // __s11 = __v9 >> 10
    
    // __t30 = blend(__v8@00000000000100000000000000, __s5@00000000000000100000000000)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(vs[8], bits["00000000000100000000000000"], t30_1);
    info.eval->multiply_plain(ss[5], bits["00000000000000100000000000"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    
    // __t31 = blend(__v9@00000000000100000000000000, __v8@00000000000000100000000000)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(vs[9], bits["00000000000100000000000000"], t31_1);
    info.eval->multiply_plain(vs[8], bits["00000000000000100000000000"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[10]); // __v10 = __t30 * __t31
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -10, gk, ss[12]); // __s12 = __v10 >> 10
    
    // __t34 = blend(__v6@00000000000000000000001000, __t32@00000000000000000000000010)
    ctxt t34_1;
    info.eval->multiply_plain(vs[6], bits["00000000000000000000001000"], t34_1);
    info.eval->add(t34_1, ts[32], ts[34]);
    
    
    // __t35 = blend(__s8@00000000000000000000001000, __t33@00000000000000000000000010)
    ctxt t35_1;
    info.eval->multiply_plain(ss[8], bits["00000000000000000000001000"], t35_1);
    info.eval->add(t35_1, ts[33], ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[11]); // __v11 = __t34 * __t35
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -18, gk, ss[13]); // __s13 = __v11 >> 18
    
    // __t36 = blend(__s0@00000000001000000000000000, __s5@00000000000000000000010000)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(ss[0], bits["00000000001000000000000000"], t36_1);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000010000"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    
    // __t37 = blend(__s6@00000000001000000000000000, __s7@00000000000000000000010000)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(ss[6], bits["00000000001000000000000000"], t37_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000000000010000"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    info.eval->add(ts[36], ts[37], vs[12]); // __v12 = __t36 + __t37
    info.eval->add(vs[12], ss[6], vs[13]); // __v13 = __v12 + __s6
    
    // __t38 = blend(__s1@00000000000000000100000000, __v13@00000000000000000000010000, __s3@00000000000000000000000010)
    ctxt t38_1, t38_2, t38_3;
    info.eval->multiply_plain(ss[1], bits["00000000000000000100000000"], t38_1);
    info.eval->multiply_plain(vs[13], bits["00000000000000000000010000"], t38_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000000010"], t38_3);
    info.eval->add_many({t38_1, t38_2, t38_3}, ts[38]);
    
    
    // __t39 = blend(__s5@00000000000000000100000000, __s12@00000000000000000000010000, __v11@00000000000000000000000010)
    ctxt t39_1, t39_2, t39_3;
    info.eval->multiply_plain(ss[5], bits["00000000000000000100000000"], t39_1);
    info.eval->multiply_plain(ss[12], bits["00000000000000000000010000"], t39_2);
    info.eval->multiply_plain(vs[11], bits["00000000000000000000000010"], t39_3);
    info.eval->add_many({t39_1, t39_2, t39_3}, ts[39]);
    
    info.eval->multiply(ts[38], ts[39], vs[14]); // __v14 = __t38 * __t39
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -19, gk, ss[14]); // __s14 = __v14 >> 19
    
    // __t40 = blend(__v9@00000000001000000000000000, __v14@00000000000000000100000010, __s9@00000000000000000000000100)
    ctxt t40_1, t40_2, t40_3;
    info.eval->multiply_plain(vs[9], bits["00000000001000000000000000"], t40_1);
    info.eval->multiply_plain(vs[14], bits["00000000000000000100000010"], t40_2);
    info.eval->multiply_plain(ss[9], bits["00000000000000000000000100"], t40_3);
    info.eval->add_many({t40_1, t40_2, t40_3}, ts[40]);
    
    
    // __t41 = blend(__v12@00000000001000000000000000, __s10@00000000000000000100000000, __v7@00000000000000000000000100, __s12@00000000000000000000000010)
    ctxt t41_1, t41_2, t41_3, t41_4;
    info.eval->multiply_plain(vs[12], bits["00000000001000000000000000"], t41_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000000100000000"], t41_2);
    info.eval->multiply_plain(vs[7], bits["00000000000000000000000100"], t41_3);
    info.eval->multiply_plain(ss[12], bits["00000000000000000000000010"], t41_4);
    info.eval->add_many({t41_1, t41_2, t41_3, t41_4}, ts[41]);
    
    info.eval->add(ts[40], ts[41], vs[15]); // __v15 = __t40 + __t41
    info.eval->rotate_rows(vs[15], -19, gk, ss[15]); // __s15 = __v15 >> 19
    info.eval->rotate_rows(vs[15], -18, gk, ss[16]); // __s16 = __v15 >> 18
    
    // __t42 = blend(__s13@00000000000000100000000000, __s16@00000000000000001000000000)
    ctxt t42_1, t42_2;
    info.eval->multiply_plain(ss[13], bits["00000000000000100000000000"], t42_1);
    info.eval->multiply_plain(ss[16], bits["00000000000000001000000000"], t42_2);
    info.eval->add(t42_1, t42_2, ts[42]);
    
    
    // __t43 = blend(__s11@00000000000000100000000000, __s15@00000000000000001000000000)
    ctxt t43_1, t43_2;
    info.eval->multiply_plain(ss[11], bits["00000000000000100000000000"], t43_1);
    info.eval->multiply_plain(ss[15], bits["00000000000000001000000000"], t43_2);
    info.eval->add(t43_1, t43_2, ts[43]);
    
    info.eval->add(ts[42], ts[43], vs[16]); // __v16 = __t42 + __t43
    info.eval->rotate_rows(vs[16], -24, gk, ss[17]); // __s17 = __v16 >> 24
    info.eval->multiply(ss[15], vs[15], vs[17]); // __v17 = __s15 * __v15
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->rotate_rows(vs[17], -4, gk, ss[18]); // __s18 = __v17 >> 4
    info.eval->add(vs[16], ss[17], vs[18]); // __v18 = __v16 + __s17
    info.eval->add(ss[14], ss[18], vs[19]); // __v19 = __s14 + __s18
    info.eval->add(vs[19], vs[18], vs[20]); // __v20 = __v19 + __v18
    return vs[20];
}
    