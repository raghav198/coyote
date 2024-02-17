
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000", info);
    add_bitstring(bits, "0011", info);
    add_bitstring(bits, "0001", info);
    add_bitstring(bits, "0110", info);
    add_bitstring(bits, "0100", info);
    add_bitstring(bits, "0010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(39);
    ts[0] = encrypt_input("11110110111111111011", info);
    ts[1] = encrypt_input("11111111111111111011", info);
    ts[2] = encrypt_input("1101101111011111", info);
    ts[3] = encrypt_input("1111101111011111", info);
    ts[4] = encrypt_input("11111111101101011110", info);
    ts[5] = encrypt_input("11111111101101011111", info);
    ts[6] = encrypt_input("11010110111101111010", info);
    ts[7] = encrypt_input("11111111111101111011", info);
    ts[8] = encrypt_input("11111111101111011111", info);
    ts[9] = encrypt_input("11111111101111011111", info);
    ts[10] = encrypt_input("111110110110", info);
    ts[11] = encrypt_input("111110110110", info);
    ts[12] = encrypt_input("11011110101111111011", info);
    ts[13] = encrypt_input("11111111101111111011", info);
    ts[18] = encrypt_input("1111011111111110", info);
    ts[19] = encrypt_input("1111111111111110", info);
    ts[23] = encrypt_input("001111111111", info);
    ts[24] = encrypt_input("001111111111", info);
    ts[26] = encrypt_input("011111011110", info);
    ts[27] = encrypt_input("011111011111", info);
    ts[28] = encrypt_input("011111011111", info);
    ts[29] = encrypt_input("011111011111", info);
    ts[32] = encrypt_input("111111111100", info);
    ts[33] = encrypt_input("111111111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[30];
    ctxt ss[0];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->add(vs[2], vs[5], vs[6]); // __v6 = __v2 + __v5
    info.eval->multiply(ts[12], ts[13], vs[7]); // __v7 = __t12 * __t13
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t14 = blend(__v3@1000, __v7@0100, __v6@0010)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(vs[3], bits["1000"], t14_1);
    info.eval->multiply_plain(vs[7], bits["0100"], t14_2);
    info.eval->multiply_plain(vs[6], bits["0010"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3}, ts[14]);
    
    
    // __t15 = blend(__v7@1000, __v0@0100, __v3@0010)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(vs[7], bits["1000"], t15_1);
    info.eval->multiply_plain(vs[0], bits["0100"], t15_2);
    info.eval->multiply_plain(vs[3], bits["0010"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[8]); // __v8 = __t14 + __t15
    
    // __t16 = blend(__v8@0110, __v3@0001)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(vs[8], bits["0110"], t16_1);
    info.eval->multiply_plain(vs[3], bits["0001"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__v3@0100, __v1@0010, __v7@0001)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(vs[3], bits["0100"], t17_1);
    info.eval->multiply_plain(vs[1], bits["0010"], t17_2);
    info.eval->multiply_plain(vs[7], bits["0001"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3}, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[9]); // __v9 = __t16 + __t17
    info.eval->add(vs[9], vs[0], vs[10]); // __v10 = __v9 + __v0
    info.eval->multiply(ts[18], ts[19], vs[11]); // __v11 = __t18 * __t19
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t20 = blend(__v8@1000, __v10@0011)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[8], bits["1000"], t20_1);
    info.eval->multiply_plain(vs[10], bits["0011"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v1@1000, __v11@0010, __v2@0001)
    ctxt t21_1, t21_2, t21_3;
    info.eval->multiply_plain(vs[1], bits["1000"], t21_1);
    info.eval->multiply_plain(vs[11], bits["0010"], t21_2);
    info.eval->multiply_plain(vs[2], bits["0001"], t21_3);
    info.eval->add_many({t21_1, t21_2, t21_3}, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[12]); // __v12 = __t20 + __t21
    
    // __t22 = blend(__v0@1000, __v4@0011)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[0], bits["1000"], t22_1);
    info.eval->multiply_plain(vs[4], bits["0011"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);
    
    info.eval->add(vs[12], ts[22], vs[13]); // __v13 = __v12 + __t22
    info.eval->multiply(ts[23], ts[24], vs[14]); // __v14 = __t23 * __t24
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->add(vs[13], vs[7], vs[15]); // __v15 = __v13 + __v7
    
    // __t25 = blend(__v15@0010, __v13@0001)
    ctxt t25_1, t25_2;
    info.eval->multiply_plain(vs[15], bits["0010"], t25_1);
    info.eval->multiply_plain(vs[13], bits["0001"], t25_2);
    info.eval->add(t25_1, t25_2, ts[25]);
    
    info.eval->add(ts[25], vs[14], vs[16]); // __v16 = __t25 + __v14
    info.eval->multiply(ts[26], ts[27], vs[17]); // __v17 = __t26 * __t27
    info.eval->relinearize_inplace(vs[17], rk);
    info.eval->multiply(ts[28], ts[29], vs[18]); // __v18 = __t28 * __t29
    info.eval->relinearize_inplace(vs[18], rk);
    
    // __t30 = blend(__v9@0100, __v16@0001)
    ctxt t30_1, t30_2;
    info.eval->multiply_plain(vs[9], bits["0100"], t30_1);
    info.eval->multiply_plain(vs[16], bits["0001"], t30_2);
    info.eval->add(t30_1, t30_2, ts[30]);
    
    
    // __t31 = blend(__v4@0100, __v17@0001)
    ctxt t31_1, t31_2;
    info.eval->multiply_plain(vs[4], bits["0100"], t31_1);
    info.eval->multiply_plain(vs[17], bits["0001"], t31_2);
    info.eval->add(t31_1, t31_2, ts[31]);
    
    info.eval->add(ts[30], ts[31], vs[19]); // __v19 = __t30 + __t31
    info.eval->add(vs[19], vs[18], vs[20]); // __v20 = __v19 + __v18
    info.eval->multiply(ts[32], ts[33], vs[21]); // __v21 = __t32 * __t33
    info.eval->relinearize_inplace(vs[21], rk);
    
    // __t34 = blend(__v13@1000, __v19@0100)
    ctxt t34_1, t34_2;
    info.eval->multiply_plain(vs[13], bits["1000"], t34_1);
    info.eval->multiply_plain(vs[19], bits["0100"], t34_2);
    info.eval->add(t34_1, t34_2, ts[34]);
    
    
    // __t35 = blend(__v21@1000, __v17@0100)
    ctxt t35_1, t35_2;
    info.eval->multiply_plain(vs[21], bits["1000"], t35_1);
    info.eval->multiply_plain(vs[17], bits["0100"], t35_2);
    info.eval->add(t35_1, t35_2, ts[35]);
    
    info.eval->add(ts[34], ts[35], vs[22]); // __v22 = __t34 + __t35
    info.eval->add(vs[22], vs[21], vs[23]); // __v23 = __v22 + __v21
    info.eval->add(vs[20], vs[1], vs[24]); // __v24 = __v20 + __v1
    
    // __t36 = blend(__v22@1000, __v23@0100)
    ctxt t36_1, t36_2;
    info.eval->multiply_plain(vs[22], bits["1000"], t36_1);
    info.eval->multiply_plain(vs[23], bits["0100"], t36_2);
    info.eval->add(t36_1, t36_2, ts[36]);
    
    info.eval->add(ts[36], vs[2], vs[25]); // __v25 = __t36 + __v2
    info.eval->add(vs[25], vs[11], vs[26]); // __v26 = __v25 + __v11
    info.eval->add(vs[26], vs[4], vs[27]); // __v27 = __v26 + __v4
    
    // __t37 = blend(__v27@1000, __v25@0100)
    ctxt t37_1, t37_2;
    info.eval->multiply_plain(vs[27], bits["1000"], t37_1);
    info.eval->multiply_plain(vs[25], bits["0100"], t37_2);
    info.eval->add(t37_1, t37_2, ts[37]);
    
    
    // __t38 = blend(__v5@1000, __v11@0100)
    ctxt t38_1, t38_2;
    info.eval->multiply_plain(vs[5], bits["1000"], t38_1);
    info.eval->multiply_plain(vs[11], bits["0100"], t38_2);
    info.eval->add(t38_1, t38_2, ts[38]);
    
    info.eval->add(ts[37], ts[38], vs[28]); // __v28 = __t37 + __t38
    info.eval->add(vs[28], vs[18], vs[29]); // __v29 = __v28 + __v18
    return vs[29];
}
    