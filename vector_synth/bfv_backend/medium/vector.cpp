
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01000001000", info);
    add_bitstring(bits, "00001000000", info);
    add_bitstring(bits, "00000000010", info);
    add_bitstring(bits, "00000000100", info);
    add_bitstring(bits, "00000001000", info);
    add_bitstring(bits, "01000000000", info);
    add_bitstring(bits, "10001000000", info);
    add_bitstring(bits, "01000010000", info);
    add_bitstring(bits, "00100100001", info);
    add_bitstring(bits, "00000010000", info);
    add_bitstring(bits, "00000010100", info);
    add_bitstring(bits, "00000000001", info);
    add_bitstring(bits, "10000000000", info);
    add_bitstring(bits, "10000000001", info);
    add_bitstring(bits, "00001100000", info);
    add_bitstring(bits, "00000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(52);
    ts[0] = encrypt_input("11001001010", info);
    ts[1] = encrypt_input("11001001010", info);
    ts[2] = encrypt_input("01001110000", info);
    ts[3] = encrypt_input("10001110000", info);
    ts[6] = encrypt_input("10000000101", info);
    ts[7] = encrypt_input("11001010101", info);
    ts[9] = encrypt_input("00000010101", info);
    ts[10] = encrypt_input("10001000001", info);
    ts[13] = encrypt_input("11001000000", info);
    ts[14] = encrypt_input("11001000011", info);
    ts[16] = encrypt_input("01010000001", info);
    ts[17] = encrypt_input("01010000000", info);
    ts[20] = encrypt_input("00010000000", info);
    ts[22] = encrypt_input("01000101000", info);
    ts[23] = encrypt_input("01000101000", info);
    ts[26] = encrypt_input("00100000001", info);
    ts[27] = encrypt_input("00100000000", info);
    ts[30] = encrypt_input("10000000010", info);
    ts[31] = encrypt_input("10000001000", info);
    ts[34] = encrypt_input("00100100100", info);
    ts[35] = encrypt_input("00001001000", info);
    ts[38] = encrypt_input("00000010000", info);
    ts[39] = encrypt_input("00000010000", info);
    ts[42] = encrypt_input("00000010000", info);
    ts[43] = encrypt_input("00000010000", info);
    ts[44] = encrypt_input("00000000100", info);
    ts[47] = encrypt_input("01000000000", info);
    ts[50] = encrypt_input("00000010000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[18];
    ctxt ss[4];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    
    // __t4 = blend(__v0@10000000000, __t2@01001110000)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["10000000000"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    
    // __t5 = blend(__v0@01000000000, __t3@10001110000)
    ctxt t5_1;
    info.eval->multiply_plain(vs[0], bits["01000000000"], t5_1);
    info.eval->add(t5_1, ts[3], ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[1]); // __v1 = __t4 + __t5
    
    // __t8 = blend(__v1@01000010000, __v0@00001000000, __t6@10000000101)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[1], bits["01000010000"], t8_1);
    info.eval->multiply_plain(vs[0], bits["00001000000"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[6]}, ts[8]);
    
    info.eval->add(ts[8], ts[7], vs[2]); // __v2 = __t8 + __t7
    
    // __t11 = blend(__v1@10001000000, __t9@00000010101)
    ctxt t11_1;
    info.eval->multiply_plain(vs[1], bits["10001000000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);
    
    
    // __t12 = blend(__v2@00000010100, __t10@10001000001)
    ctxt t12_1;
    info.eval->multiply_plain(vs[2], bits["00000010100"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    info.eval->add(ts[11], ts[12], vs[3]); // __v3 = __t11 + __t12
    
    // __t15 = blend(__v0@00000000010, __v3@00000000001, __t13@11001000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[0], bits["00000000010"], t15_1);
    info.eval->multiply_plain(vs[3], bits["00000000001"], t15_2);
    info.eval->add_many({t15_1, t15_2, ts[13]}, ts[15]);
    
    info.eval->add(ts[15], ts[14], vs[4]); // __v4 = __t15 + __t14
    
    // __t18 = blend(__v4@10000000000, __t16@01010000001)
    ctxt t18_1;
    info.eval->multiply_plain(vs[4], bits["10000000000"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    
    // __t19 = blend(__v2@10000000001, __t17@01010000000)
    ctxt t19_1;
    info.eval->multiply_plain(vs[2], bits["10000000001"], t19_1);
    info.eval->add(t19_1, ts[17], ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[5]); // __v5 = __t18 * __t19
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t21 = blend(__v4@01000000000, __t20@00010000000)
    ctxt t21_1;
    info.eval->multiply_plain(vs[4], bits["01000000000"], t21_1);
    info.eval->add(t21_1, ts[20], ts[21]);
    
    info.eval->multiply(vs[5], ts[21], vs[6]); // __v6 = __v5 * __t21
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -9, gk, ss[0]); // __s0 = __v6 >> 9
    
    // __t24 = blend(__v3@10000000000, __v4@00001000000, __t22@01000101000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[3], bits["10000000000"], t24_1);
    info.eval->multiply_plain(vs[4], bits["00001000000"], t24_2);
    info.eval->add_many({t24_1, t24_2, ts[22]}, ts[24]);
    
    
    // __t25 = blend(__v5@10000000000, __v3@00001000000, __t23@01000101000)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(vs[5], bits["10000000000"], t25_1);
    info.eval->multiply_plain(vs[3], bits["00001000000"], t25_2);
    info.eval->add_many({t25_1, t25_2, ts[23]}, ts[25]);
    
    info.eval->add(ts[24], ts[25], vs[7]); // __v7 = __t24 + __t25
    
    // __t28 = blend(__v2@01000000000, __v7@00001100000, __v0@00000001000, __t26@00100000001)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[2], bits["01000000000"], t28_1);
    info.eval->multiply_plain(vs[7], bits["00001100000"], t28_2);
    info.eval->multiply_plain(vs[0], bits["00000001000"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3, ts[26]}, ts[28]);
    
    
    // __t29 = blend(__v6@01000000000, __v2@00001000000, __v1@00000100000, __v7@00000001000, __v5@00000000001, __t27@00100000000)
    ctxt t29_1, t29_2, t29_3, t29_4, t29_5;
    info.eval->multiply_plain(vs[6], bits["01000000000"], t29_1);
    info.eval->multiply_plain(vs[2], bits["00001000000"], t29_2);
    info.eval->multiply_plain(vs[1], bits["00000100000"], t29_3);
    info.eval->multiply_plain(vs[7], bits["00000001000"], t29_4);
    info.eval->multiply_plain(vs[5], bits["00000000001"], t29_5);
    info.eval->add_many({t29_1, t29_2, t29_3, t29_4, t29_5, ts[27]}, ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[8]); // __v8 = __t28 * __t29
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t32 = blend(__v8@01000001000, __t30@10000000010)
    ctxt t32_1;
    info.eval->multiply_plain(vs[8], bits["01000001000"], t32_1);
    info.eval->add(t32_1, ts[30], ts[32]);
    
    
    // __t33 = blend(__v7@01000000000, __v4@00000000010, __t31@10000001000)
    ctxt t33_1, t33_2;
    info.eval->multiply_plain(vs[7], bits["01000000000"], t33_1);
    info.eval->multiply_plain(vs[4], bits["00000000010"], t33_2);
    info.eval->add_many({t33_1, t33_2, ts[31]}, ts[33]);
    
    info.eval->add(ts[32], ts[33], vs[9]); // __v9 = __t32 + __t33
    
    // __t36 = blend(__v7@10000000000, __v8@00001000000, __v9@00000001000, __v4@00000000001, __t34@00100100100)
    ctxt t36_1, t36_2, t36_3, t36_4;
    info.eval->multiply_plain(vs[7], bits["10000000000"], t36_1);
    info.eval->multiply_plain(vs[8], bits["00001000000"], t36_2);
    info.eval->multiply_plain(vs[9], bits["00000001000"], t36_3);
    info.eval->multiply_plain(vs[4], bits["00000000001"], t36_4);
    info.eval->add_many({t36_1, t36_2, t36_3, t36_4, ts[34]}, ts[36]);
    
    
    // __t37 = blend(__v9@10000000000, __v8@00100100001, __v3@00000000100, __t35@00001001000)
    ctxt t37_1, t37_2, t37_3;
    info.eval->multiply_plain(vs[9], bits["10000000000"], t37_1);
    info.eval->multiply_plain(vs[8], bits["00100100001"], t37_2);
    info.eval->multiply_plain(vs[3], bits["00000000100"], t37_3);
    info.eval->add_many({t37_1, t37_2, t37_3, ts[35]}, ts[37]);
    
    info.eval->multiply(ts[36], ts[37], vs[10]); // __v10 = __t36 * __t37
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -10, gk, ss[1]); // __s1 = __v10 >> 10
    info.eval->rotate_rows(vs[10], -2, gk, ss[2]); // __s2 = __v10 >> 2
    info.eval->rotate_rows(vs[10], -1, gk, ss[3]); // __s3 = __v10 >> 1
    info.eval->add(vs[3], ts[38], vs[11]); // __v11 = __v3 + __t38
    
    // __t40 = blend(__v10@00000000100, __t39@00000010000)
    ctxt t40_1;
    info.eval->multiply_plain(vs[10], bits["00000000100"], t40_1);
    info.eval->add(t40_1, ts[39], ts[40]);
    
    
    // __t41 = blend(__s3@00000010000, __v10@00000000100)
    ctxt t41_1, t41_2;
    info.eval->multiply_plain(ss[3], bits["00000010000"], t41_1);
    info.eval->multiply_plain(vs[10], bits["00000000100"], t41_2);
    info.eval->add(t41_1, t41_2, ts[41]);
    
    info.eval->multiply(ts[40], ts[41], vs[12]); // __v12 = __t40 * __t41
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->add(ts[42], ts[43], vs[13]); // __v13 = __t42 + __t43
    
    // __t45 = blend(__s1@01000000000, __s2@00000010000, __t44@00000000100)
    ctxt t45_1, t45_2;
    info.eval->multiply_plain(ss[1], bits["01000000000"], t45_1);
    info.eval->multiply_plain(ss[2], bits["00000010000"], t45_2);
    info.eval->add_many({t45_1, t45_2, ts[44]}, ts[45]);
    
    
    // __t46 = blend(__s0@01000000000, __v12@00000010100)
    ctxt t46_1, t46_2;
    info.eval->multiply_plain(ss[0], bits["01000000000"], t46_1);
    info.eval->multiply_plain(vs[12], bits["00000010100"], t46_2);
    info.eval->add(t46_1, t46_2, ts[46]);
    
    info.eval->multiply(ts[45], ts[46], vs[14]); // __v14 = __t45 * __t46
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->multiply(vs[11], vs[13], vs[15]); // __v15 = __v11 * __v13
    info.eval->relinearize_inplace(vs[15], rk);
    
    // __t48 = blend(__v14@00000010000, __t47@01000000000)
    ctxt t48_1;
    info.eval->multiply_plain(vs[14], bits["00000010000"], t48_1);
    info.eval->add(t48_1, ts[47], ts[48]);
    
    
    // __t49 = blend(__v9@01000000000, __v15@00000010000)
    ctxt t49_1, t49_2;
    info.eval->multiply_plain(vs[9], bits["01000000000"], t49_1);
    info.eval->multiply_plain(vs[15], bits["00000010000"], t49_2);
    info.eval->add(t49_1, t49_2, ts[49]);
    
    info.eval->multiply(ts[48], ts[49], vs[16]); // __v16 = __t48 * __t49
    info.eval->relinearize_inplace(vs[16], rk);
    
    // __t51 = blend(__v14@01000000000, __t50@00000010000)
    ctxt t51_1;
    info.eval->multiply_plain(vs[14], bits["01000000000"], t51_1);
    info.eval->add(t51_1, ts[50], ts[51]);
    
    info.eval->multiply(ts[51], vs[16], vs[17]); // __v17 = __t51 * __v16
    info.eval->relinearize_inplace(vs[17], rk);
    return vs[17];
}
    