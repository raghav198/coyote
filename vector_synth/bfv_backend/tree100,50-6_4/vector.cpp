
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000001", info);
    add_bitstring(bits, "0010000", info);
    add_bitstring(bits, "0100000", info);
    add_bitstring(bits, "0010100", info);
    add_bitstring(bits, "0000010", info);
    add_bitstring(bits, "0001000", info);
    add_bitstring(bits, "1000100", info);
    add_bitstring(bits, "0100100", info);
    add_bitstring(bits, "0000100", info);
    add_bitstring(bits, "0000101", info);
    add_bitstring(bits, "1000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(44);
    ts[0] = encrypt_input("0111101111111111111", info);
    ts[1] = encrypt_input("011111111111111111", info);
    ts[2] = encrypt_input("11111111111100111111", info);
    ts[3] = encrypt_input("11110111111111111110", info);
    ts[4] = encrypt_input("00001100111", info);
    ts[5] = encrypt_input("00001110111", info);
    ts[8] = encrypt_input("011011111100", info);
    ts[9] = encrypt_input("011101110100", info);
    ts[10] = encrypt_input("00111011100", info);
    ts[11] = encrypt_input("00111011100", info);
    ts[12] = encrypt_input("000010101000", info);
    ts[13] = encrypt_input("0000110111", info);
    ts[14] = encrypt_input("11100011100", info);
    ts[15] = encrypt_input("100011100", info);
    ts[18] = encrypt_input("000001010", info);
    ts[19] = encrypt_input("000001110", info);
    ts[22] = encrypt_input("111011100110", info);
    ts[23] = encrypt_input("1110101001110", info);
    ts[26] = encrypt_input("011101000", info);
    ts[27] = encrypt_input("01110111000", info);
    ts[30] = encrypt_input("111000000", info);
    ts[31] = encrypt_input("111000000", info);
    ts[34] = encrypt_input("000011100", info);
    ts[35] = encrypt_input("000011100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[21];
    ctxt ss[6];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t6 = blend(__v0@0010000, __v1@0000010, __t4@0000101)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["0010000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["0000010"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v1@0010000, __v0@0000010, __t5@0000101)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["0010000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["0000010"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->add(ts[8], ts[9], vs[3]); // __v3 = __t8 + __t9
    info.eval->add(ts[10], ts[11], vs[4]); // __v4 = __t10 + __t11
    info.eval->add(ts[12], ts[13], vs[5]); // __v5 = __t12 + __t13
    
    // __t16 = blend(__v3@0001000, __v2@0000001, __t14@1000100)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(vs[3], bits["0001000"], t16_1);
    info.eval->multiply_plain(vs[2], bits["0000001"], t16_2);
    info.eval->add_many({t16_1, t16_2, ts[14]}, ts[16]);
    
    
    // __t17 = blend(__v0@0001000, __v5@0000001, __t15@1000100)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[0], bits["0001000"], t17_1);
    info.eval->multiply_plain(vs[5], bits["0000001"], t17_2);
    info.eval->add_many({t17_1, t17_2, ts[15]}, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[6]); // __v6 = __t16 * __t17
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t20 = blend(__v1@0000101, __t18@0000010)
    ctxt t20_1;
    info.eval->multiply_plain(vs[1], bits["0000101"], t20_1);
    info.eval->add(t20_1, ts[18], ts[20]);
    
    
    // __t21 = blend(__v0@0000101, __t19@0000010)
    ctxt t21_1;
    info.eval->multiply_plain(vs[0], bits["0000101"], t21_1);
    info.eval->add(t21_1, ts[19], ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[7]); // __v7 = __t20 + __t21
    
    // __t24 = blend(__v0@0100000, __v6@0000100, __t22@1010010)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[0], bits["0100000"], t24_1);
    info.eval->multiply_plain(vs[6], bits["0000100"], t24_2);
    info.eval->add_many({t24_1, t24_2, ts[22]}, ts[24]);
    
    
    // __t25 = blend(__v3@0100100, __t23@1010010)
    ctxt t25_1;
    info.eval->multiply_plain(vs[3], bits["0100100"], t25_1);
    info.eval->add(t25_1, ts[23], ts[25]);
    
    info.eval->multiply(ts[24], ts[25], vs[8]); // __v8 = __t24 * __t25
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t28 = blend(__v1@1000000, __v7@0000100, __v8@0000010, __t26@0101000)
    ctxt t28_1, t28_2, t28_3;
    info.eval->multiply_plain(vs[1], bits["1000000"], t28_1);
    info.eval->multiply_plain(vs[7], bits["0000100"], t28_2);
    info.eval->multiply_plain(vs[8], bits["0000010"], t28_3);
    info.eval->add_many({t28_1, t28_2, t28_3, ts[26]}, ts[28]);
    
    
    // __t29 = blend(__v8@1000100, __v7@0000010, __t27@0101000)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(vs[8], bits["1000100"], t29_1);
    info.eval->multiply_plain(vs[7], bits["0000010"], t29_2);
    info.eval->add_many({t29_1, t29_2, ts[27]}, ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[9]); // __v9 = __t28 * __t29
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t32 = blend(__v9@0100000, __v4@0010100, __t30@1000000)
    ctxt t32_1, t32_2;
    info.eval->multiply_plain(vs[9], bits["0100000"], t32_1);
    info.eval->multiply_plain(vs[4], bits["0010100"], t32_2);
    info.eval->add_many({t32_1, t32_2, ts[30]}, ts[32]);
    
    
    // __t33 = blend(__v1@0100000, __v8@0010000, __v5@0000100, __t31@1000000)
    ctxt t33_1, t33_2, t33_3;
    info.eval->multiply_plain(vs[1], bits["0100000"], t33_1);
    info.eval->multiply_plain(vs[8], bits["0010000"], t33_2);
    info.eval->multiply_plain(vs[5], bits["0000100"], t33_3);
    info.eval->add_many({t33_1, t33_2, t33_3, ts[31]}, ts[33]);
    
    info.eval->add(ts[32], ts[33], vs[10]); // __v10 = __t32 + __t33
    
    // __t36 = blend(__v10@1000000, __v8@0100000, __t34@0000100)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(vs[10], bits["1000000"], t36_1);
    info.eval->multiply_plain(vs[8], bits["0100000"], t36_2);
    info.eval->add_many({t36_1, t36_2, ts[34]}, ts[36]);
    
    
    // __t37 = blend(__v6@1000000, __v10@0100000, __t35@0000100)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(vs[6], bits["1000000"], t37_1);
    info.eval->multiply_plain(vs[10], bits["0100000"], t37_2);
    info.eval->add_many({t37_1, t37_2, ts[35]}, ts[37]);
    
    info.eval->add(ts[36], ts[37], vs[11]); // __v11 = __t36 + __t37
    info.eval->rotate_rows(vs[11], -6, gk, ss[0]); // __s0 = __v11 >> 6
    
    // __t38 = blend(__v2@0010000, __v9@0001000, __v11@0000100)
    ctxt t38_1, t38_2, t38_3;
    info.eval->multiply_plain(vs[2], bits["0010000"], t38_1);
    info.eval->multiply_plain(vs[9], bits["0001000"], t38_2);
    info.eval->multiply_plain(vs[11], bits["0000100"], t38_3);
    info.eval->add_many({t38_1, t38_2, t38_3}, ts[38]);
    
    
    // __t39 = blend(__v10@0010000, __v1@0001000, __v2@0000100)
    ctxt t39_1, t39_2, t39_3;
    info.eval->multiply_plain(vs[10], bits["0010000"], t39_1);
    info.eval->multiply_plain(vs[1], bits["0001000"], t39_2);
    info.eval->multiply_plain(vs[2], bits["0000100"], t39_3);
    info.eval->add_many({t39_1, t39_2, t39_3}, ts[39]);
    
    info.eval->add(ts[38], ts[39], vs[12]); // __v12 = __t38 + __t39
    info.eval->rotate_rows(vs[12], -5, gk, ss[1]); // __s1 = __v12 >> 5
    
    // __t40 = blend(__v11@1000000, __v12@0000100, __v6@0000001)
    ctxt t40_1, t40_2, t40_3;
    info.eval->multiply_plain(vs[11], bits["1000000"], t40_1);
    info.eval->multiply_plain(vs[12], bits["0000100"], t40_2);
    info.eval->multiply_plain(vs[6], bits["0000001"], t40_3);
    info.eval->add_many({t40_1, t40_2, t40_3}, ts[40]);
    
    
    // __t41 = blend(__v9@1000000, __v10@0000100, __v7@0000001)
    ctxt t41_1, t41_2, t41_3;
    info.eval->multiply_plain(vs[9], bits["1000000"], t41_1);
    info.eval->multiply_plain(vs[10], bits["0000100"], t41_2);
    info.eval->multiply_plain(vs[7], bits["0000001"], t41_3);
    info.eval->add_many({t41_1, t41_2, t41_3}, ts[41]);
    
    info.eval->add(ts[40], ts[41], vs[13]); // __v13 = __t40 + __t41
    info.eval->rotate_rows(vs[13], -1, gk, ss[2]); // __s2 = __v13 >> 1
    
    // __t42 = blend(__v12@0001000, __v9@0000100, __v2@0000010)
    ctxt t42_1, t42_2, t42_3;
    info.eval->multiply_plain(vs[12], bits["0001000"], t42_1);
    info.eval->multiply_plain(vs[9], bits["0000100"], t42_2);
    info.eval->multiply_plain(vs[2], bits["0000010"], t42_3);
    info.eval->add_many({t42_1, t42_2, t42_3}, ts[42]);
    
    
    // __t43 = blend(__v6@0001000, __v13@0000100, __v9@0000010)
    ctxt t43_1, t43_2, t43_3;
    info.eval->multiply_plain(vs[6], bits["0001000"], t43_1);
    info.eval->multiply_plain(vs[13], bits["0000100"], t43_2);
    info.eval->multiply_plain(vs[9], bits["0000010"], t43_3);
    info.eval->add_many({t43_1, t43_2, t43_3}, ts[43]);
    
    info.eval->multiply(ts[42], ts[43], vs[14]); // __v14 = __t42 * __t43
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -4, gk, ss[3]); // __s3 = __v14 >> 4
    info.eval->rotate_rows(vs[14], -3, gk, ss[4]); // __s4 = __v14 >> 3
    info.eval->rotate_rows(vs[14], -2, gk, ss[5]); // __s5 = __v14 >> 2
    info.eval->add(ss[3], ss[5], vs[15]); // __v15 = __s3 + __s5
    info.eval->add(vs[15], ss[4], vs[16]); // __v16 = __v15 + __s4
    info.eval->multiply(ss[2], vs[13], vs[17]); // __v17 = __s2 * __v13
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->add(ss[0], ss[1], vs[18]); // __v18 = __s0 + __s1
    info.eval->add(vs[17], vs[18], vs[19]); // __v19 = __v17 + __v18
    info.eval->add(vs[19], vs[16], vs[20]); // __v20 = __v19 + __v16
    return vs[20];
}
    