
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100000000000000000000000", info);
    add_bitstring(bits, "101000000000000000000000", info);
    add_bitstring(bits, "001000000000000000000000", info);
    add_bitstring(bits, "000000000000001000000000", info);
    add_bitstring(bits, "000000000000101000000000", info);
    add_bitstring(bits, "000000000000100000000000", info);
    add_bitstring(bits, "001000000000001000000000", info);
    add_bitstring(bits, "101000000000100000000000", info);
    add_bitstring(bits, "100000000000100000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(45);
    ts[0] = encrypt_input("110111101011111111111111111110110111101111011111111101111111111111111111111111100000111110111110", info);
    ts[1] = encrypt_input("110111101011111111111111111110110111101111011111111101111111111111111111111111100000111110111110", info);
    ts[2] = encrypt_input("110111101011111111111111111110110111101111011111111101011110110111101011011110101111111110111111111011011111111101111111", info);
    ts[3] = encrypt_input("110111101011111111111111111110110111101111011111111101011110110111101011011110101111111110111111111011011111111101111111", info);
    ts[4] = encrypt_input("11110011111000000000000000000000", info);
    ts[5] = encrypt_input("1111001111100000000011111011111000000000", info);
    ts[7] = encrypt_input("0000000000000011110000000000", info);
    ts[8] = encrypt_input("0000000000000011110000000000", info);
    ts[11] = encrypt_input("0011111000000000000000000000", info);
    ts[12] = encrypt_input("00111110000000000011111000000000", info);
    ts[17] = encrypt_input("11111000000000001111100000000000", info);
    ts[18] = encrypt_input("11111000000000001111100000000000", info);
    ts[21] = encrypt_input("11111000000000001111000000000000", info);
    ts[22] = encrypt_input("11111000000000001111100000000000", info);
    ts[28] = encrypt_input("00111100000000000011111000000000", info);
    ts[29] = encrypt_input("001111100000000011111011111000000000", info);
    ts[32] = encrypt_input("00000000000011111011110000000000", info);
    ts[37] = encrypt_input("00000000000011111011111000000000", info);
    ts[38] = encrypt_input("00000000000011111011111000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[19];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -23, gk, ss[0]); // __s0 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -20, gk, ss[1]); // __s1 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -19, gk, ss[2]); // __s2 = __v0 >> 19
    info.eval->rotate_rows(vs[0], -16, gk, ss[3]); // __s3 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -15, gk, ss[4]); // __s4 = __v0 >> 15
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -23, gk, ss[5]); // __s5 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -20, gk, ss[6]); // __s6 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -19, gk, ss[7]); // __s7 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -16, gk, ss[8]); // __s8 = __v1 >> 16
    info.eval->rotate_rows(vs[1], -15, gk, ss[9]); // __s9 = __v1 >> 15
    
    // __t6 = blend(__s9@000000000000101000000000, __t4@101000000000000000000000)
    ctxt t6_1;
    info.eval->multiply_plain(ss[9], bits["000000000000101000000000"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    info.eval->multiply(ts[6], ts[5], vs[2]); // __v2 = __t6 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t9 = blend(__s8@100000000000000000000000, __s9@001000000000000000000000, __v1@000000000000100000000000, __t7@000000000000001000000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[8], bits["100000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[9], bits["001000000000000000000000"], t9_2);
    info.eval->multiply_plain(vs[1], bits["000000000000100000000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3, ts[7]}, ts[9]);
    
    
    // __t10 = blend(__s3@100000000000000000000000, __s4@001000000000000000000000, __v0@000000000000100000000000, __t8@000000000000001000000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[3], bits["100000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[4], bits["001000000000000000000000"], t10_2);
    info.eval->multiply_plain(vs[0], bits["000000000000100000000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3, ts[8]}, ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[3]); // __v3 = __t9 * __t10
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t13 = blend(__s5@100000000000000000000000, __s8@000000000000100000000000, __s6@000000000000001000000000, __t11@001000000000000000000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[5], bits["100000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[8], bits["000000000000100000000000"], t13_2);
    info.eval->multiply_plain(ss[6], bits["000000000000001000000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3, ts[11]}, ts[13]);
    
    
    // __t14 = blend(__s0@100000000000000000000000, __s3@000000000000100000000000, __t12@001000000000001000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[0], bits["100000000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[3], bits["000000000000100000000000"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[12]}, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[4]); // __v4 = __t13 * __t14
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t15 = blend(__v1@100000000000000000000000, __s6@001000000000000000000000, __s5@000000000000100000000000, __s8@000000000000001000000000)
    ctxt t15_1, t15_2, t15_3, t15_4;
    info.eval->multiply_plain(vs[1], bits["100000000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[6], bits["001000000000000000000000"], t15_2);
    info.eval->multiply_plain(ss[5], bits["000000000000100000000000"], t15_3);
    info.eval->multiply_plain(ss[8], bits["000000000000001000000000"], t15_4);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4}, ts[15]);
    
    
    // __t16 = blend(__v0@100000000000000000000000, __s1@001000000000000000000000, __s0@000000000000100000000000, __s3@000000000000001000000000)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(vs[0], bits["100000000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[1], bits["001000000000000000000000"], t16_2);
    info.eval->multiply_plain(ss[0], bits["000000000000100000000000"], t16_3);
    info.eval->multiply_plain(ss[3], bits["000000000000001000000000"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4}, ts[16]);
    
    info.eval->multiply(ts[15], ts[16], vs[5]); // __v5 = __t15 * __t16
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t19 = blend(__s7@001000000000000000000000, __s5@000000000000001000000000, __t17@100000000000100000000000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(ss[7], bits["001000000000000000000000"], t19_1);
    info.eval->multiply_plain(ss[5], bits["000000000000001000000000"], t19_2);
    info.eval->add_many({t19_1, t19_2, ts[17]}, ts[19]);
    
    
    // __t20 = blend(__s2@001000000000000000000000, __s0@000000000000001000000000, __t18@100000000000100000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(ss[2], bits["001000000000000000000000"], t20_1);
    info.eval->multiply_plain(ss[0], bits["000000000000001000000000"], t20_2);
    info.eval->add_many({t20_1, t20_2, ts[18]}, ts[20]);
    
    info.eval->multiply(ts[19], ts[20], vs[6]); // __v6 = __t19 * __t20
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t23 = blend(__s8@001000000000000000000000, __v1@000000000000001000000000, __t21@100000000000100000000000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(ss[8], bits["001000000000000000000000"], t23_1);
    info.eval->multiply_plain(vs[1], bits["000000000000001000000000"], t23_2);
    info.eval->add_many({t23_1, t23_2, ts[21]}, ts[23]);
    
    
    // __t24 = blend(__s3@001000000000000000000000, __v0@000000000000001000000000, __t22@100000000000100000000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(ss[3], bits["001000000000000000000000"], t24_1);
    info.eval->multiply_plain(vs[0], bits["000000000000001000000000"], t24_2);
    info.eval->add_many({t24_1, t24_2, ts[22]}, ts[24]);
    
    info.eval->multiply(ts[23], ts[24], vs[7]); // __v7 = __t23 * __t24
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t25 = blend(__v4@100000000000000000000000, __v7@001000000000000000000000, __v5@000000000000100000000000, __v6@000000000000001000000000)
    ctxt t25_1, t25_2, t25_3, t25_4;
    info.eval->multiply_plain(vs[4], bits["100000000000000000000000"], t25_1);
    info.eval->multiply_plain(vs[7], bits["001000000000000000000000"], t25_2);
    info.eval->multiply_plain(vs[5], bits["000000000000100000000000"], t25_3);
    info.eval->multiply_plain(vs[6], bits["000000000000001000000000"], t25_4);
    info.eval->add_many({t25_1, t25_2, t25_3, t25_4}, ts[25]);
    
    
    // __t26 = blend(__v5@100000000000000000000000, __v6@001000000000000000000000, __v3@000000000000100000000000, __v7@000000000000001000000000)
    ctxt t26_1, t26_2, t26_3, t26_4;
    info.eval->multiply_plain(vs[5], bits["100000000000000000000000"], t26_1);
    info.eval->multiply_plain(vs[6], bits["001000000000000000000000"], t26_2);
    info.eval->multiply_plain(vs[3], bits["000000000000100000000000"], t26_3);
    info.eval->multiply_plain(vs[7], bits["000000000000001000000000"], t26_4);
    info.eval->add_many({t26_1, t26_2, t26_3, t26_4}, ts[26]);
    
    info.eval->add(ts[25], ts[26], vs[8]); // __v8 = __t25 + __t26
    
    // __t27 = blend(__v3@100000000000000000000000, __v5@001000000000001000000000, __v4@000000000000100000000000)
    ctxt t27_1, t27_2, t27_3;
    info.eval->multiply_plain(vs[3], bits["100000000000000000000000"], t27_1);
    info.eval->multiply_plain(vs[5], bits["001000000000001000000000"], t27_2);
    info.eval->multiply_plain(vs[4], bits["000000000000100000000000"], t27_3);
    info.eval->add_many({t27_1, t27_2, t27_3}, ts[27]);
    
    info.eval->add(vs[8], ts[27], vs[9]); // __v9 = __v8 + __t27
    
    // __t30 = blend(__s7@100000000000100000000000, __t28@001000000000001000000000)
    ctxt t30_1;
    info.eval->multiply_plain(ss[7], bits["100000000000100000000000"], t30_1);
    info.eval->add(t30_1, ts[28], ts[30]);
    
    
    // __t31 = blend(__s2@100000000000000000000000, __t29@001000000000101000000000)
    ctxt t31_1;
    info.eval->multiply_plain(ss[2], bits["100000000000000000000000"], t31_1);
    info.eval->add(t31_1, ts[29], ts[31]);
    
    info.eval->multiply(ts[30], ts[31], vs[10]); // __v10 = __t30 * __t31
    info.eval->relinearize_inplace(vs[10], rk);
    
    // __t33 = blend(__s6@100000000000100000000000, __s5@001000000000000000000000, __s7@000000000000001000000000)
    ctxt t33_1, t33_2, t33_3;
    info.eval->multiply_plain(ss[6], bits["100000000000100000000000"], t33_1);
    info.eval->multiply_plain(ss[5], bits["001000000000000000000000"], t33_2);
    info.eval->multiply_plain(ss[7], bits["000000000000001000000000"], t33_3);
    info.eval->add_many({t33_1, t33_2, t33_3}, ts[33]);
    
    
    // __t34 = blend(__s1@100000000000000000000000, __s0@001000000000000000000000, __t32@000000000000101000000000)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(ss[1], bits["100000000000000000000000"], t34_1);
    info.eval->multiply_plain(ss[0], bits["001000000000000000000000"], t34_2);
    info.eval->add_many({t34_1, t34_2, ts[32]}, ts[34]);
    
    info.eval->multiply(ts[33], ts[34], vs[11]); // __v11 = __t33 * __t34
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t35 = blend(__v10@100000000000100000000000, __v3@001000000000000000000000, __v11@000000000000001000000000)
    ctxt t35_1, t35_2, t35_3;
    info.eval->multiply_plain(vs[10], bits["100000000000100000000000"], t35_1);
    info.eval->multiply_plain(vs[3], bits["001000000000000000000000"], t35_2);
    info.eval->multiply_plain(vs[11], bits["000000000000001000000000"], t35_3);
    info.eval->add_many({t35_1, t35_2, t35_3}, ts[35]);
    
    info.eval->add(vs[9], ts[35], vs[12]); // __v12 = __v9 + __t35
    
    // __t36 = blend(__v11@101000000000100000000000, __v4@000000000000001000000000)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(vs[11], bits["101000000000100000000000"], t36_1);
    info.eval->multiply_plain(vs[4], bits["000000000000001000000000"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    info.eval->add(vs[12], ts[36], vs[13]); // __v13 = __v12 + __t36
    
    // __t39 = blend(__s9@100000000000000000000000, __v1@001000000000000000000000, __t37@000000000000101000000000)
    ctxt t39_1, t39_2;
    info.eval->multiply_plain(ss[9], bits["100000000000000000000000"], t39_1);
    info.eval->multiply_plain(vs[1], bits["001000000000000000000000"], t39_2);
    info.eval->add_many({t39_1, t39_2, ts[37]}, ts[39]);
    
    
    // __t40 = blend(__s4@100000000000000000000000, __v0@001000000000000000000000, __t38@000000000000101000000000)
    ctxt t40_1, t40_2;
    info.eval->multiply_plain(ss[4], bits["100000000000000000000000"], t40_1);
    info.eval->multiply_plain(vs[0], bits["001000000000000000000000"], t40_2);
    info.eval->add_many({t40_1, t40_2, ts[38]}, ts[40]);
    
    info.eval->multiply(ts[39], ts[40], vs[14]); // __v14 = __t39 * __t40
    info.eval->relinearize_inplace(vs[14], rk);
    
    // __t41 = blend(__v14@101000000000000000000000, __v2@000000000000101000000000)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(vs[14], bits["101000000000000000000000"], t41_1);
    info.eval->multiply_plain(vs[2], bits["000000000000101000000000"], t41_2);
    info.eval->add(t41_1, t41_2, ts[41]);
    
    info.eval->add(vs[13], ts[41], vs[15]); // __v15 = __v13 + __t41
    
    // __t42 = blend(__v2@100000000000000000000000, __v10@001000000000000000000000, __v7@000000000000100000000000, __v3@000000000000001000000000)
    ctxt t42_1, t42_2, t42_3, t42_4;
    info.eval->multiply_plain(vs[2], bits["100000000000000000000000"], t42_1);
    info.eval->multiply_plain(vs[10], bits["001000000000000000000000"], t42_2);
    info.eval->multiply_plain(vs[7], bits["000000000000100000000000"], t42_3);
    info.eval->multiply_plain(vs[3], bits["000000000000001000000000"], t42_4);
    info.eval->add_many({t42_1, t42_2, t42_3, t42_4}, ts[42]);
    
    info.eval->add(vs[15], ts[42], vs[16]); // __v16 = __v15 + __t42
    
    // __t43 = blend(__v7@100000000000000000000000, __v4@001000000000000000000000, __v6@000000000000100000000000, __v14@000000000000001000000000)
    ctxt t43_1, t43_2, t43_3, t43_4;
    info.eval->multiply_plain(vs[7], bits["100000000000000000000000"], t43_1);
    info.eval->multiply_plain(vs[4], bits["001000000000000000000000"], t43_2);
    info.eval->multiply_plain(vs[6], bits["000000000000100000000000"], t43_3);
    info.eval->multiply_plain(vs[14], bits["000000000000001000000000"], t43_4);
    info.eval->add_many({t43_1, t43_2, t43_3, t43_4}, ts[43]);
    
    info.eval->add(vs[16], ts[43], vs[17]); // __v17 = __v16 + __t43
    
    // __t44 = blend(__v6@100000000000000000000000, __v2@001000000000000000000000, __v14@000000000000100000000000, __v10@000000000000001000000000)
    ctxt t44_1, t44_2, t44_3, t44_4;
    info.eval->multiply_plain(vs[6], bits["100000000000000000000000"], t44_1);
    info.eval->multiply_plain(vs[2], bits["001000000000000000000000"], t44_2);
    info.eval->multiply_plain(vs[14], bits["000000000000100000000000"], t44_3);
    info.eval->multiply_plain(vs[10], bits["000000000000001000000000"], t44_4);
    info.eval->add_many({t44_1, t44_2, t44_3, t44_4}, ts[44]);
    
    info.eval->add(vs[17], ts[44], vs[18]); // __v18 = __v17 + __t44
    return vs[18];
}
    