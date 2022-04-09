
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "001010000000000000000000000", info);
    add_bitstring(bits, "000000001000000000000000000", info);
    add_bitstring(bits, "000000000000000000001000000", info);
    add_bitstring(bits, "000000000000000010000000000", info);
    add_bitstring(bits, "000000000000000001000000000", info);
    add_bitstring(bits, "000000000010000000000000000", info);
    add_bitstring(bits, "000000000000000000000001000", info);
    add_bitstring(bits, "000000000000000000000010000", info);
    add_bitstring(bits, "000000100000000000000000000", info);
    add_bitstring(bits, "000000000000000100000000000", info);
    add_bitstring(bits, "000010000000000000000000000", info);
    add_bitstring(bits, "000000100000000000001000000", info);
    add_bitstring(bits, "000000000000001000000000000", info);
    add_bitstring(bits, "000000000010000010000000000", info);
    add_bitstring(bits, "000100000000000000000000000", info);
    add_bitstring(bits, "001000000000000000000000000", info);
    add_bitstring(bits, "100000000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(45);
    ts[0] = encrypt_input("0000000000000011100000110000000", info);
    ts[1] = encrypt_input("0000000000000011100000110000000", info);
    ts[2] = encrypt_input("001110001100111000001110011100000111000", info);
    ts[3] = encrypt_input("0011000011001011000001110011100000111000", info);
    ts[4] = encrypt_input("00011111011100000000001110111111110001110", info);
    ts[5] = encrypt_input("0001111011100000000001101111111110001110", info);
    ts[8] = encrypt_input("00000111001110111000010100000000000", info);
    ts[9] = encrypt_input("0000011100110111000011100000000000", info);
    ts[12] = encrypt_input("0000000111000000000000000000111", info);
    ts[13] = encrypt_input("0000000111000000000000000000111", info);
    ts[16] = encrypt_input("0011100000000000011000000100000", info);
    ts[17] = encrypt_input("001110000000000001110000001110000", info);
    ts[20] = encrypt_input("0011101110000000000000000000000", info);
    ts[21] = encrypt_input("001110110000000000000000000000", info);
    ts[24] = encrypt_input("0000000000100000001100000000000", info);
    ts[25] = encrypt_input("0000000000110000001110000000000", info);
    ts[30] = encrypt_input("00111000000000000000000000000", info);
    ts[31] = encrypt_input("00111000000000000000000000000", info);
    ts[32] = encrypt_input("1100000000000000101000000000000", info);
    ts[33] = encrypt_input("1010000000000000111000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[20];
    ctxt ss[15];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t6 = blend(__v0@000000000000001000000000000, __t4@000110100000000001011100010)
    ctxt t6_1;
    info.eval->multiply_plain(vs[0], bits["000000000000001000000000000"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v1@000000000000001000000000000, __t5@000110100000000001011100010)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["000000000000001000000000000"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -24, gk, ss[0]); // __s0 = __v2 >> 24
    info.eval->rotate_rows(vs[2], -22, gk, ss[1]); // __s1 = __v2 >> 22
    
    // __t10 = blend(__v2@000000100000000000001000000, __v1@000000000000000001000000000, __t8@000001001010000100000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[2], bits["000000100000000000001000000"], t10_1);
    info.eval->multiply_plain(vs[1], bits["000000000000000001000000000"], t10_2);
    info.eval->add_many({t10_1, t10_2, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__v1@000000100000000000000000000, __v2@000000000000000001000000000, __v0@000000000000000000001000000, __t9@000001001010000100000000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[1], bits["000000100000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[2], bits["000000000000000001000000000"], t11_2);
    info.eval->multiply_plain(vs[0], bits["000000000000000000001000000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -24, gk, ss[2]); // __s2 = __v3 >> 24
    
    // __t14 = blend(__v3@000000001000000000000000000, __t12@000000010000000000000000001)
    ctxt t14_1;
    info.eval->multiply_plain(vs[3], bits["000000001000000000000000000"], t14_1);
    info.eval->add(t14_1, ts[12], ts[14]);
    
    
    // __t15 = blend(__v1@000000001000000000000000000, __t13@000000010000000000000000001)
    ctxt t15_1;
    info.eval->multiply_plain(vs[1], bits["000000001000000000000000000"], t15_1);
    info.eval->add(t15_1, ts[13], ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[4]); // __v4 = __t14 * __t15
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -22, gk, ss[3]); // __s3 = __v4 >> 22
    info.eval->rotate_rows(vs[4], -24, gk, ss[4]); // __s4 = __v4 >> 24
    
    // __t18 = blend(__s2@000000000000000001000000000, __t16@001000000000000100000010000)
    ctxt t18_1;
    info.eval->multiply_plain(ss[2], bits["000000000000000001000000000"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    
    // __t19 = blend(__v3@000000000000000001000000000, __t17@001000000000000100000010000)
    ctxt t19_1;
    info.eval->multiply_plain(vs[3], bits["000000000000000001000000000"], t19_1);
    info.eval->add(t19_1, ts[17], ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[5]); // __v5 = __t18 + __t19
    info.eval->rotate_rows(vs[5], -25, gk, ss[5]); // __s5 = __v5 >> 25
    
    // __t22 = blend(__v5@000000000000000000000010000, __t20@001010000000000000000000000)
    ctxt t22_1;
    info.eval->multiply_plain(vs[5], bits["000000000000000000000010000"], t22_1);
    info.eval->add(t22_1, ts[20], ts[22]);
    
    
    // __t23 = blend(__s0@000000000000000000000010000, __t21@001010000000000000000000000)
    ctxt t23_1;
    info.eval->multiply_plain(ss[0], bits["000000000000000000000010000"], t23_1);
    info.eval->add(t23_1, ts[21], ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[6]); // __v6 = __t22 * __t23
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -19, gk, ss[6]); // __s6 = __v6 >> 19
    
    // __t26 = blend(__s3@001000000000000000000000000, __v5@000000000000000100000000000, __s4@000000000000000000000001000, __t24@000000000010000010000000000)
    ctxt t26_1, t26_2, t26_3;
    info.eval->multiply_plain(ss[3], bits["001000000000000000000000000"], t26_1);
    info.eval->multiply_plain(vs[5], bits["000000000000000100000000000"], t26_2);
    info.eval->multiply_plain(ss[4], bits["000000000000000000000001000"], t26_3);
    info.eval->add_many({t26_1, t26_2, t26_3, ts[24]}, ts[26]);
    
    
    // __t27 = blend(__v5@001000000000000000000000000, __v3@000000000000000100000000000, __v1@000000000000000000000001000, __t25@000000000010000010000000000)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(vs[5], bits["001000000000000000000000000"], t27_1);
    info.eval->multiply_plain(vs[3], bits["000000000000000100000000000"], t27_2);
    info.eval->multiply_plain(vs[1], bits["000000000000000000000001000"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3, ts[25]}, ts[27]);
    
    info.eval->add(ts[26], ts[27], vs[7]); // __v7 = __t26 + __t27
    info.eval->rotate_rows(vs[7], -25, gk, ss[7]); // __s7 = __v7 >> 25
    info.eval->rotate_rows(vs[7], -19, gk, ss[8]); // __s8 = __v7 >> 19
    
    // __t28 = blend(__v1@001000000000000000000000000, __v2@000010000000000000000000000, __v7@000000000010000010000000000)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[1], bits["001000000000000000000000000"], t28_1);
    info.eval->multiply_plain(vs[2], bits["000010000000000000000000000"], t28_2);
    info.eval->multiply_plain(vs[7], bits["000000000010000010000000000"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3}, ts[28]);
    
    
    // __t29 = blend(__v6@001010000000000000000000000, __v3@000000000010000000000000000, __s1@000000000000000010000000000)
    ctxt t29_1, t29_2, t29_3;
    info.eval->multiply_plain(vs[6], bits["001010000000000000000000000"], t29_1);
    info.eval->multiply_plain(vs[3], bits["000000000010000000000000000"], t29_2);
    info.eval->multiply_plain(ss[1], bits["000000000000000010000000000"], t29_3);
    info.eval->add_many({t29_1, t29_2, t29_3}, ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[8]); // __v8 = __t28 * __t29
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -25, gk, ss[9]); // __s9 = __v8 >> 25
    info.eval->rotate_rows(vs[8], -19, gk, ss[10]); // __s10 = __v8 >> 19
    info.eval->multiply(ts[30], ts[31], vs[9]); // __v9 = __t30 * __t31
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t34 = blend(__v9@001000000000000000000000000, __t32@100000000000001000000000000)
    ctxt t34_1;
    info.eval->multiply_plain(vs[9], bits["001000000000000000000000000"], t34_1);
    info.eval->add(t34_1, ts[32], ts[34]);
    
    
    // __t35 = blend(__s2@001000000000000000000000000, __t33@100000000000001000000000000)
    ctxt t35_1;
    info.eval->multiply_plain(ss[2], bits["001000000000000000000000000"], t35_1);
    info.eval->add(t35_1, ts[33], ts[35]);
    
    info.eval->add(ts[34], ts[35], vs[10]); // __v10 = __t34 + __t35
    
    // __t36 = blend(__s9@001000000000000000000000000, __s1@000000000000001000000000000)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(ss[9], bits["001000000000000000000000000"], t36_1);
    info.eval->multiply_plain(ss[1], bits["000000000000001000000000000"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    info.eval->add(ts[36], vs[10], vs[11]); // __v11 = __t36 + __v10
    
    // __t37 = blend(__v10@100000000000000000000000000, __s10@001000000000000000000000000, __s6@000000000000001000000000000)
    ctxt t37_1, t37_2, t37_3;
    info.eval->multiply_plain(vs[10], bits["100000000000000000000000000"], t37_1);
    info.eval->multiply_plain(ss[10], bits["001000000000000000000000000"], t37_2);
    info.eval->multiply_plain(ss[6], bits["000000000000001000000000000"], t37_3);
    info.eval->add_many({t37_1, t37_2, t37_3}, ts[37]);
    
    
    // __t38 = blend(__s0@100000000000000000000000000, __v8@001000000000000000000000000, __v11@000000000000001000000000000)
    ctxt t38_1, t38_2, t38_3;
    info.eval->multiply_plain(ss[0], bits["100000000000000000000000000"], t38_1);
    info.eval->multiply_plain(vs[8], bits["001000000000000000000000000"], t38_2);
    info.eval->multiply_plain(vs[11], bits["000000000000001000000000000"], t38_3);
    info.eval->add_many({t38_1, t38_2, t38_3}, ts[38]);
    
    info.eval->multiply(ts[37], ts[38], vs[12]); // __v12 = __t37 * __t38
    info.eval->relinearize_inplace(vs[12], rk);
    
    // __t39 = blend(__v12@100000000000000000000000000, __v11@001000000000000000000000000, __v2@000000000000001000000000000)
    ctxt t39_1, t39_2, t39_3;
    info.eval->multiply_plain(vs[12], bits["100000000000000000000000000"], t39_1);
    info.eval->multiply_plain(vs[11], bits["001000000000000000000000000"], t39_2);
    info.eval->multiply_plain(vs[2], bits["000000000000001000000000000"], t39_3);
    info.eval->add_many({t39_1, t39_2, t39_3}, ts[39]);
    
    
    // __t40 = blend(__s7@100000000000000000000000000, __v12@001000000000000000000000000, __s9@000000000000001000000000000)
    ctxt t40_1, t40_2, t40_3;
    info.eval->multiply_plain(ss[7], bits["100000000000000000000000000"], t40_1);
    info.eval->multiply_plain(vs[12], bits["001000000000000000000000000"], t40_2);
    info.eval->multiply_plain(ss[9], bits["000000000000001000000000000"], t40_3);
    info.eval->add_many({t40_1, t40_2, t40_3}, ts[40]);
    
    info.eval->add(ts[39], ts[40], vs[13]); // __v13 = __t39 + __t40
    info.eval->rotate_rows(vs[13], -3, gk, ss[11]); // __s11 = __v13 >> 3
    info.eval->rotate_rows(vs[13], -1, gk, ss[12]); // __s12 = __v13 >> 1
    info.eval->multiply(vs[12], vs[13], vs[14]); // __v14 = __v12 * __v13
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -1, gk, ss[13]); // __s13 = __v14 >> 1
    info.eval->multiply(ss[8], vs[7], vs[15]); // __v15 = __s8 * __v7
    info.eval->relinearize_inplace(vs[15], rk);
    
    // __t41 = blend(__s2@000100000000000000000000000, __v15@000000000000000100000000000)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(ss[2], bits["000100000000000000000000000"], t41_1);
    info.eval->multiply_plain(vs[15], bits["000000000000000100000000000"], t41_2);
    info.eval->add(t41_1, t41_2, ts[41]);
    
    
    // __t42 = blend(__s3@000100000000000000000000000, __s5@000000000000000100000000000)
    ctxt t42_1, t42_2;
    info.eval->multiply_plain(ss[3], bits["000100000000000000000000000"], t42_1);
    info.eval->multiply_plain(ss[5], bits["000000000000000100000000000"], t42_2);
    info.eval->add(t42_1, t42_2, ts[42]);
    
    info.eval->add(ts[41], ts[42], vs[16]); // __v16 = __t41 + __t42
    info.eval->add(vs[16], ss[11], vs[17]); // __v17 = __v16 + __s11
    
    // __t43 = blend(__s12@000100000000000000000000000, __s13@000000000000000100000000000)
    ctxt t43_1, t43_2;
    info.eval->multiply_plain(ss[12], bits["000100000000000000000000000"], t43_1);
    info.eval->multiply_plain(ss[13], bits["000000000000000100000000000"], t43_2);
    info.eval->add(t43_1, t43_2, ts[43]);
    
    
    // __t44 = blend(__v17@000100000000000000000000000, __v16@000000000000000100000000000)
    ctxt t44_1, t44_2;
    info.eval->multiply_plain(vs[17], bits["000100000000000000000000000"], t44_1);
    info.eval->multiply_plain(vs[16], bits["000000000000000100000000000"], t44_2);
    info.eval->add(t44_1, t44_2, ts[44]);
    
    info.eval->multiply(ts[43], ts[44], vs[18]); // __v18 = __t43 * __t44
    info.eval->relinearize_inplace(vs[18], rk);
    info.eval->rotate_rows(vs[18], -12, gk, ss[14]); // __s14 = __v18 >> 12
    info.eval->multiply(vs[18], ss[14], vs[19]); // __v19 = __v18 * __s14
    info.eval->relinearize_inplace(vs[19], rk);
    return vs[19];
}
    