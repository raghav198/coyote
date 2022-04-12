
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000001", info);
    add_bitstring(bits, "0100000", info);
    add_bitstring(bits, "1000001", info);
    add_bitstring(bits, "1100000", info);
    add_bitstring(bits, "0100001", info);
    add_bitstring(bits, "1000000", info);
    add_bitstring(bits, "0000010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(40);
    ts[0] = encrypt_input("000000111", info);
    ts[1] = encrypt_input("000000111", info);
    ts[2] = encrypt_input("01110000111", info);
    ts[3] = encrypt_input("01110000111", info);
    ts[4] = encrypt_input("11100001110", info);
    ts[5] = encrypt_input("11100001110", info);
    ts[8] = encrypt_input("011100000", info);
    ts[9] = encrypt_input("000000111", info);
    ts[12] = encrypt_input("111000000", info);
    ts[13] = encrypt_input("1111100000", info);
    ts[14] = encrypt_input("11111100000", info);
    ts[15] = encrypt_input("011100000", info);
    ts[16] = encrypt_input("0100100000", info);
    ts[17] = encrypt_input("111000000", info);
    ts[20] = encrypt_input("000000111", info);
    ts[23] = encrypt_input("11110010000110", info);
    ts[24] = encrypt_input("011100000", info);
    ts[26] = encrypt_input("110000000", info);
    ts[27] = encrypt_input("000000111", info);
    ts[29] = encrypt_input("00000011", info);
    ts[30] = encrypt_input("00000101111", info);
    ts[32] = encrypt_input("000000111", info);
    ts[33] = encrypt_input("000001110", info);
    ts[36] = encrypt_input("000000111", info);
    ts[39] = encrypt_input("000001110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[19];
    ctxt ss[3];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    
    // __t6 = blend(__v1@0000001, __t4@1000010)
    ctxt t6_1;
    info.eval->multiply_plain(vs[1], bits["0000001"], t6_1);
    info.eval->add(t6_1, ts[4], ts[6]);
    
    
    // __t7 = blend(__v0@0000001, __t5@1000010)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["0000001"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t10 = blend(__v2@0000001, __t8@0100000)
    ctxt t10_1;
    info.eval->multiply_plain(vs[2], bits["0000001"], t10_1);
    info.eval->add(t10_1, ts[8], ts[10]);
    
    
    // __t11 = blend(__v1@0100000, __t9@0000001)
    ctxt t11_1;
    info.eval->multiply_plain(vs[1], bits["0100000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[3]); // __v3 = __t10 + __t11
    info.eval->multiply(ts[12], vs[2], vs[4]); // __v4 = __t12 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->add(ts[13], ts[14], vs[5]); // __v5 = __t13 + __t14
    info.eval->add(vs[5], ts[15], vs[6]); // __v6 = __v5 + __t15
    
    // __t18 = blend(__v5@1000000, __t16@0100000)
    ctxt t18_1;
    info.eval->multiply_plain(vs[5], bits["1000000"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    
    // __t19 = blend(__v6@0100000, __t17@1000000)
    ctxt t19_1;
    info.eval->multiply_plain(vs[6], bits["0100000"], t19_1);
    info.eval->add(t19_1, ts[17], ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[7]); // __v7 = __t18 + __t19
    
    // __t21 = blend(__v4@1000000, __v3@0100001)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[4], bits["1000000"], t21_1);
    info.eval->multiply_plain(vs[3], bits["0100001"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    
    // __t22 = blend(__v7@1100000, __t20@0000001)
    ctxt t22_1;
    info.eval->multiply_plain(vs[7], bits["1100000"], t22_1);
    info.eval->add(t22_1, ts[20], ts[22]);
    
    info.eval->multiply(ts[21], ts[22], vs[8]); // __v8 = __t21 * __t22
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t25 = blend(__v8@1000001, __t24@0100000)
    ctxt t25_1;
    info.eval->multiply_plain(vs[8], bits["1000001"], t25_1);
    info.eval->add(t25_1, ts[24], ts[25]);
    
    info.eval->add(ts[23], ts[25], vs[9]); // __v9 = __t23 + __t25
    info.eval->multiply(ts[26], vs[9], vs[10]); // __v10 = __t26 * __v9
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -5, gk, ss[0]); // __s0 = __v10 >> 5
    
    // __t28 = blend(__v8@0100000, __t27@0000001)
    ctxt t28_1;
    info.eval->multiply_plain(vs[8], bits["0100000"], t28_1);
    info.eval->add(t28_1, ts[27], ts[28]);
    
    info.eval->add(vs[9], ts[28], vs[11]); // __v11 = __v9 + __t28
    info.eval->rotate_rows(vs[11], -5, gk, ss[1]); // __s1 = __v11 >> 5
    
    // __t31 = blend(__s0@0000010, __t29@0000001)
    ctxt t31_1;
    info.eval->multiply_plain(ss[0], bits["0000010"], t31_1);
    info.eval->add(t31_1, ts[29], ts[31]);
    
    info.eval->add(ts[31], ts[30], vs[12]); // __v12 = __t31 + __t30
    info.eval->add(ts[32], vs[12], vs[13]); // __v13 = __t32 + __v12
    info.eval->add(vs[13], vs[11], vs[14]); // __v14 = __v13 + __v11
    
    // __t34 = blend(__v14@0000001, __t33@0000010)
    ctxt t34_1;
    info.eval->multiply_plain(vs[14], bits["0000001"], t34_1);
    info.eval->add(t34_1, ts[33], ts[34]);
    
    
    // __t35 = blend(__v12@0000010, __s1@0000001)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[12], bits["0000010"], t35_1);
    info.eval->multiply_plain(ss[1], bits["0000001"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->multiply(ts[34], ts[35], vs[15]); // __v15 = __t34 * __t35
    info.eval->relinearize_inplace(vs[15], rk);
    
    // __t37 = blend(__v2@0000010, __v15@0000001)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(vs[2], bits["0000010"], t37_1);
    info.eval->multiply_plain(vs[15], bits["0000001"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    
    // __t38 = blend(__v15@0000010, __t36@0000001)
    ctxt t38_1;
    info.eval->multiply_plain(vs[15], bits["0000010"], t38_1);
    info.eval->add(t38_1, ts[36], ts[38]);
    
    info.eval->multiply(ts[37], ts[38], vs[16]); // __v16 = __t37 * __t38
    info.eval->relinearize_inplace(vs[16], rk);
    info.eval->rotate_rows(vs[16], -6, gk, ss[2]); // __s2 = __v16 >> 6
    info.eval->multiply(vs[16], ts[39], vs[17]); // __v17 = __v16 * __t39
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->multiply(ss[2], vs[17], vs[18]); // __v18 = __s2 * __v17
    info.eval->relinearize_inplace(vs[18], rk);
    return vs[18];
}
    