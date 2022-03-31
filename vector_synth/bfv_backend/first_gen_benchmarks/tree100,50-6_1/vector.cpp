
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "10000000000000000", info);
    add_bitstring(bits, "00000000100000000", info);
    add_bitstring(bits, "00000000000100000", info);
    add_bitstring(bits, "00000000000001000", info);
    add_bitstring(bits, "00010000000100000", info);
    add_bitstring(bits, "00010000000000000", info);
    add_bitstring(bits, "01000000000000000", info);
    add_bitstring(bits, "00000000000000010", info);
    add_bitstring(bits, "00000000010000000", info);
    add_bitstring(bits, "01000000000100000", info);
    add_bitstring(bits, "00000001000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(51);
    ts[0] = encrypt_input("0011100001110001110011100", info);
    ts[1] = encrypt_input("00110000011100010010011000", info);
    ts[2] = encrypt_input("110001110011100001010111000", info);
    ts[3] = encrypt_input("11001010011100001110111000", info);
    ts[4] = encrypt_input("000000011100011100000", info);
    ts[5] = encrypt_input("000000011100011100000", info);
    ts[6] = encrypt_input("0000000000010111110000", info);
    ts[7] = encrypt_input("000000000001111110000", info);
    ts[10] = encrypt_input("0000000000010100111000", info);
    ts[11] = encrypt_input("000000000001010111000", info);
    ts[12] = encrypt_input("01000000000011000000", info);
    ts[13] = encrypt_input("011100000000011000000", info);
    ts[14] = encrypt_input("11111001110000000100000", info);
    ts[15] = encrypt_input("10111011100000001100000", info);
    ts[16] = encrypt_input("0000000000000000111", info);
    ts[17] = encrypt_input("0000000000000000111", info);
    ts[20] = encrypt_input("0000000011100000000", info);
    ts[21] = encrypt_input("0000000011100000000", info);
    ts[24] = encrypt_input("000000000010000001110", info);
    ts[25] = encrypt_input("000000000011000001110", info);
    ts[28] = encrypt_input("00011100000001110001110", info);
    ts[29] = encrypt_input("00011100000001110001110", info);
    ts[30] = encrypt_input("0000111100000000000", info);
    ts[31] = encrypt_input("000011111100000000000", info);
    ts[34] = encrypt_input("0001110000000000000", info);
    ts[35] = encrypt_input("0001100000000000000", info);
    ts[38] = encrypt_input("0000000001110000000", info);
    ts[39] = encrypt_input("0000000001110000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[25];
    ctxt ss[20];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -12, gk, ss[1]); // __s1 = __v0 >> 12
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t8 = blend(__v0@00000001000000000, __t6@00000000000110000)
    ctxt t8_1;
    info.eval->multiply_plain(vs[0], bits["00000001000000000"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    
    // __t9 = blend(__v2@00000001000000000, __t7@00000000000110000)
    ctxt t9_1;
    info.eval->multiply_plain(vs[2], bits["00000001000000000"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -1, gk, ss[3]); // __s3 = __v3 >> 1
    info.eval->rotate_rows(vs[3], -12, gk, ss[4]); // __s4 = __v3 >> 12
    info.eval->add(ts[10], ts[11], vs[4]); // __v4 = __t10 + __t11
    info.eval->add(ts[12], ts[13], vs[5]); // __v5 = __t12 + __t13
    info.eval->add(ts[14], ts[15], vs[6]); // __v6 = __t14 + __t15
    
    // __t18 = blend(__v6@00000000000100000, __t16@00000000000000001)
    ctxt t18_1;
    info.eval->multiply_plain(vs[6], bits["00000000000100000"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    
    // __t19 = blend(__v0@00000000000100000, __t17@00000000000000001)
    ctxt t19_1;
    info.eval->multiply_plain(vs[0], bits["00000000000100000"], t19_1);
    info.eval->add(t19_1, ts[17], ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[7]); // __v7 = __t18 * __t19
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -12, gk, ss[5]); // __s5 = __v7 >> 12
    
    // __t22 = blend(__v1@10000000000000000, __v2@00000000000100000, __t20@00000000100000000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[1], bits["10000000000000000"], t22_1);
    info.eval->multiply_plain(vs[2], bits["00000000000100000"], t22_2);
    info.eval->add_many({t22_1, t22_2, ts[20]}, ts[22]);
    
    
    // __t23 = blend(__v6@10000000000000000, __v4@00000000000100000, __t21@00000000100000000)
    ctxt t23_1, t23_2;
    info.eval->multiply_plain(vs[6], bits["10000000000000000"], t23_1);
    info.eval->multiply_plain(vs[4], bits["00000000000100000"], t23_2);
    info.eval->add_many({t23_1, t23_2, ts[21]}, ts[23]);
    
    info.eval->multiply(ts[22], ts[23], vs[8]); // __v8 = __t22 * __t23
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -7, gk, ss[6]); // __s6 = __v8 >> 7
    info.eval->rotate_rows(vs[8], -3, gk, ss[7]); // __s7 = __v8 >> 3
    
    // __t26 = blend(__v3@00000000000100000, __v1@00000000000001000, __t24@00000000001000010)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(vs[3], bits["00000000000100000"], t26_1);
    info.eval->multiply_plain(vs[1], bits["00000000000001000"], t26_2);
    info.eval->add_many({t26_1, t26_2, ts[24]}, ts[26]);
    
    
    // __t27 = blend(__v1@00000000000100000, __v4@00000000000001000, __t25@00000000001000010)
    ctxt t27_1, t27_2;
    info.eval->multiply_plain(vs[1], bits["00000000000100000"], t27_1);
    info.eval->multiply_plain(vs[4], bits["00000000000001000"], t27_2);
    info.eval->add_many({t27_1, t27_2, ts[25]}, ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[9]); // __v9 = __t26 * __t27
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -1, gk, ss[8]); // __s8 = __v9 >> 1
    info.eval->rotate_rows(vs[9], -12, gk, ss[9]); // __s9 = __v9 >> 12
    info.eval->add(ts[28], ts[29], vs[10]); // __v10 = __t28 + __t29
    
    // __t32 = blend(__v5@01000000000100000, __v6@00010000000000000, __v10@00000000000000010, __t30@00001100000000000)
    ctxt t32_1, t32_2, t32_3;
    info.eval->multiply_plain(vs[5], bits["01000000000100000"], t32_1);
    info.eval->multiply_plain(vs[6], bits["00010000000000000"], t32_2);
    info.eval->multiply_plain(vs[10], bits["00000000000000010"], t32_3);
    info.eval->add_many({t32_1, t32_2, t32_3, ts[30]}, ts[32]);
    
    
    // __t33 = blend(__v6@01000000000000000, __v10@00010000000100000, __v9@00000000000000010, __t31@00001100000000000)
    ctxt t33_1, t33_2, t33_3;
    info.eval->multiply_plain(vs[6], bits["01000000000000000"], t33_1);
    info.eval->multiply_plain(vs[10], bits["00010000000100000"], t33_2);
    info.eval->multiply_plain(vs[9], bits["00000000000000010"], t33_3);
    info.eval->add_many({t33_1, t33_2, t33_3, ts[31]}, ts[33]);
    
    info.eval->multiply(ts[32], ts[33], vs[11]); // __v11 = __t32 * __t33
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -7, gk, ss[10]); // __s10 = __v11 >> 7
    info.eval->rotate_rows(vs[11], -3, gk, ss[11]); // __s11 = __v11 >> 3
    info.eval->rotate_rows(vs[11], -12, gk, ss[12]); // __s12 = __v11 >> 12
    
    // __t36 = blend(__v9@00000000000100000, __t34@00010000000000000)
    ctxt t36_1;
    info.eval->multiply_plain(vs[9], bits["00000000000100000"], t36_1);
    info.eval->add(t36_1, ts[34], ts[36]);
    
    
    // __t37 = blend(__v11@00000000000100000, __t35@00010000000000000)
    ctxt t37_1;
    info.eval->multiply_plain(vs[11], bits["00000000000100000"], t37_1);
    info.eval->add(t37_1, ts[35], ts[37]);
    
    info.eval->add(ts[36], ts[37], vs[12]); // __v12 = __t36 + __t37
    
    // __t40 = blend(__v1@00010000000000000, __v8@00000000000100000, __t38@00000000010000000)
    ctxt t40_1, t40_2;
    info.eval->multiply_plain(vs[1], bits["00010000000000000"], t40_1);
    info.eval->multiply_plain(vs[8], bits["00000000000100000"], t40_2);
    info.eval->add_many({t40_1, t40_2, ts[38]}, ts[40]);
    
    
    // __t41 = blend(__v12@00010000000000000, __v7@00000000000100000, __t39@00000000010000000)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(vs[12], bits["00010000000000000"], t41_1);
    info.eval->multiply_plain(vs[7], bits["00000000000100000"], t41_2);
    info.eval->add_many({t41_1, t41_2, ts[39]}, ts[41]);
    
    info.eval->add(ts[40], ts[41], vs[13]); // __v13 = __t40 + __t41
    info.eval->rotate_rows(vs[13], -16, gk, ss[13]); // __s13 = __v13 >> 16
    
    // __t42 = blend(__v11@00010000000000000, __v12@00000000000100000)
    ctxt t42_1, t42_2;
    info.eval->multiply_plain(vs[11], bits["00010000000000000"], t42_1);
    info.eval->multiply_plain(vs[12], bits["00000000000100000"], t42_2);
    info.eval->add(t42_1, t42_2, ts[42]);
    
    info.eval->add(ts[42], vs[13], vs[14]); // __v14 = __t42 + __v13
    info.eval->rotate_rows(vs[14], -7, gk, ss[14]); // __s14 = __v14 >> 7
    info.eval->rotate_rows(vs[14], -14, gk, ss[15]); // __s15 = __v14 >> 14
    
    // __t43 = blend(__s10@00000000100000000, __s0@00000000010000000, __s8@00000000000100000)
    ctxt t43_1, t43_2, t43_3;
    info.eval->multiply_plain(ss[10], bits["00000000100000000"], t43_1);
    info.eval->multiply_plain(ss[0], bits["00000000010000000"], t43_2);
    info.eval->multiply_plain(ss[8], bits["00000000000100000"], t43_3);
    info.eval->add_many({t43_1, t43_2, t43_3}, ts[43]);
    
    
    // __t44 = blend(__s9@00000000100000000, __s1@00000000010000000, __s7@00000000000100000)
    ctxt t44_1, t44_2, t44_3;
    info.eval->multiply_plain(ss[9], bits["00000000100000000"], t44_1);
    info.eval->multiply_plain(ss[1], bits["00000000010000000"], t44_2);
    info.eval->multiply_plain(ss[7], bits["00000000000100000"], t44_3);
    info.eval->add_many({t44_1, t44_2, t44_3}, ts[44]);
    
    info.eval->multiply(ts[43], ts[44], vs[15]); // __v15 = __t43 * __t44
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->rotate_rows(vs[15], -1, gk, ss[16]); // __s16 = __v15 >> 1
    
    // __t45 = blend(__s11@00000000100000000, __s10@00000000000100000)
    ctxt t45_1, t45_2;
    info.eval->multiply_plain(ss[11], bits["00000000100000000"], t45_1);
    info.eval->multiply_plain(ss[10], bits["00000000000100000"], t45_2);
    info.eval->add(t45_1, t45_2, ts[45]);
    
    
    // __t46 = blend(__s13@00000000100000000, __s5@00000000000100000)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(ss[13], bits["00000000100000000"], t46_1);
    info.eval->multiply_plain(ss[5], bits["00000000000100000"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    info.eval->add(ts[45], ts[46], vs[16]); // __v16 = __t45 + __t46
    info.eval->add(ss[3], vs[16], vs[17]); // __v17 = __s3 + __v16
    
    // __t47 = blend(__s4@00000001000000000, __v15@00000000100000000)
    ctxt t47_1, t47_2;
    info.eval->multiply_plain(ss[4], bits["00000001000000000"], t47_1);
    info.eval->multiply_plain(vs[15], bits["00000000100000000"], t47_2);
    info.eval->add(t47_1, t47_2, ts[47]);
    
    
    // __t48 = blend(__s2@00000001000000000, __v17@00000000100000000)
    ctxt t48_1, t48_2;
    info.eval->multiply_plain(ss[2], bits["00000001000000000"], t48_1);
    info.eval->multiply_plain(vs[17], bits["00000000100000000"], t48_2);
    info.eval->add(t48_1, t48_2, ts[48]);
    
    info.eval->add(ts[47], ts[48], vs[18]); // __v18 = __t47 + __t48
    
    // __t49 = blend(__s6@00000001000000000, __v18@00000000100000000, __v16@00000000000100000)
    ctxt t49_1, t49_2, t49_3;
    info.eval->multiply_plain(ss[6], bits["00000001000000000"], t49_1);
    info.eval->multiply_plain(vs[18], bits["00000000100000000"], t49_2);
    info.eval->multiply_plain(vs[16], bits["00000000000100000"], t49_3);
    info.eval->add_many({t49_1, t49_2, t49_3}, ts[49]);
    
    
    // __t50 = blend(__v18@00000001000000000, __s15@00000000100000000, __v15@00000000000100000)
    ctxt t50_1, t50_2, t50_3;
    info.eval->multiply_plain(vs[18], bits["00000001000000000"], t50_1);
    info.eval->multiply_plain(ss[15], bits["00000000100000000"], t50_2);
    info.eval->multiply_plain(vs[15], bits["00000000000100000"], t50_3);
    info.eval->add_many({t50_1, t50_2, t50_3}, ts[50]);
    
    info.eval->multiply(ts[49], ts[50], vs[19]); // __v19 = __t49 * __t50
    info.eval->relinearize_inplace(vs[19], rk);
    info.eval->rotate_rows(vs[19], -3, gk, ss[17]); // __s17 = __v19 >> 3
    info.eval->rotate_rows(vs[19], -2, gk, ss[18]); // __s18 = __v19 >> 2
    info.eval->rotate_rows(vs[19], -16, gk, ss[19]); // __s19 = __v19 >> 16
    info.eval->multiply(ss[19], ss[17], vs[20]); // __v20 = __s19 * __s17
    info.eval->relinearize_inplace(vs[20], rk);
    info.eval->add(ss[16], ss[12], vs[21]); // __v21 = __s16 + __s12
    info.eval->add(vs[21], ss[14], vs[22]); // __v22 = __v21 + __s14
    info.eval->multiply(vs[20], vs[22], vs[23]); // __v23 = __v20 * __v22
    info.eval->relinearize_inplace(vs[23], rk);
    info.eval->multiply(vs[23], ss[18], vs[24]); // __v24 = __v23 * __s18
    info.eval->relinearize_inplace(vs[24], rk);
    return vs[24];
}
    