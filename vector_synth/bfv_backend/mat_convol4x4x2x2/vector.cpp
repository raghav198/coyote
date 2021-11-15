
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000011000010100", info);
    add_bitstring(bits, "0000000000000010", info);
    add_bitstring(bits, "1000010000000000", info);
    add_bitstring(bits, "0000010000010001", info);
    add_bitstring(bits, "0000000000010000", info);
    add_bitstring(bits, "0010000000000001", info);
    add_bitstring(bits, "0000000000000110", info);
    add_bitstring(bits, "0000011000000000", info);
    add_bitstring(bits, "1000000000000001", info);
    add_bitstring(bits, "0010000100010010", info);
    add_bitstring(bits, "0000000100000100", info);
    add_bitstring(bits, "1010000000000000", info);
    add_bitstring(bits, "1000011000000100", info);
    add_bitstring(bits, "0010001000000000", info);
    add_bitstring(bits, "0000000100000000", info);
    add_bitstring(bits, "1000000000000000", info);
    add_bitstring(bits, "1000001000000000", info);
    add_bitstring(bits, "0010000100000011", info);
    add_bitstring(bits, "0010010100010111", info);
    add_bitstring(bits, "1000010100010010", info);
    add_bitstring(bits, "0000000100010111", info);
    add_bitstring(bits, "0000000000000100", info);
    add_bitstring(bits, "0000000000000101", info);
    add_bitstring(bits, "0010000000000010", info);
    add_bitstring(bits, "1000000000000100", info);
    add_bitstring(bits, "0000001100000000", info);
    add_bitstring(bits, "0000010000000000", info);
    add_bitstring(bits, "0000010000000001", info);
    add_bitstring(bits, "0010000000000000", info);
    add_bitstring(bits, "0000000000000001", info);
    add_bitstring(bits, "0000000000000011", info);
    add_bitstring(bits, "0000001000000101", info);
    add_bitstring(bits, "0000001000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(16);
    ts[0] = encrypt_input("11111111101111111111111111111011111111111111111011111111101111110110101111111011", info);
    ts[2] = encrypt_input("00011110011111110111101000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[25];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -5, gk, ss[0]); // __s0 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -14, gk, ss[1]); // __s1 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -4, gk, ss[3]); // __s3 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -15, gk, ss[4]); // __s4 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -12, gk, ss[5]); // __s5 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -1, gk, ss[6]); // __s6 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[7]); // __s7 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -8, gk, ss[8]); // __s8 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -3, gk, ss[9]); // __s9 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -2, gk, ss[10]); // __s10 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -3, gk, ss[11]); // __s11 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -4, gk, ss[12]); // __s12 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -8, gk, ss[13]); // __s13 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -10, gk, ss[14]); // __s14 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -11, gk, ss[15]); // __s15 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -12, gk, ss[16]); // __s16 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -13, gk, ss[17]); // __s17 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -15, gk, ss[18]); // __s18 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -1, gk, ss[19]); // __s19 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -6, gk, ss[20]); // __s20 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -9, gk, ss[21]); // __s21 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -5, gk, ss[22]); // __s22 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -7, gk, ss[23]); // __s23 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -14, gk, ss[24]); // __s24 = __v1 >> 14
    
    // __t4 = blend(__s14@1000000000000100, __s15@0010000000000010, __s18@0000011000000000, __s12@0000000100000000, __s13@0000000000010000, __s16@0000000000000001)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6;
    info.eval->multiply_plain(ss[14], bits["1000000000000100"], t4_1);
    info.eval->multiply_plain(ss[15], bits["0010000000000010"], t4_2);
    info.eval->multiply_plain(ss[18], bits["0000011000000000"], t4_3);
    info.eval->multiply_plain(ss[12], bits["0000000100000000"], t4_4);
    info.eval->multiply_plain(ss[13], bits["0000000000010000"], t4_5);
    info.eval->multiply_plain(ss[16], bits["0000000000000001"], t4_6);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6}, ts[4]);
    
    
    // __t5 = blend(__s8@1010000000000000, __s0@0000010000000001, __s2@0000001000000000, __s6@0000000100000100, __s9@0000000000010000, __s1@0000000000000010)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6;
    info.eval->multiply_plain(ss[8], bits["1010000000000000"], t5_1);
    info.eval->multiply_plain(ss[0], bits["0000010000000001"], t5_2);
    info.eval->multiply_plain(ss[2], bits["0000001000000000"], t5_3);
    info.eval->multiply_plain(ss[6], bits["0000000100000100"], t5_4);
    info.eval->multiply_plain(ss[9], bits["0000000000010000"], t5_5);
    info.eval->multiply_plain(ss[1], bits["0000000000000010"], t5_6);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s15@1000000000000000, __s16@0010000000000000, __s10@0000010000000000, __s19@0000001100000000, __s22@0000000000010000, __s20@0000000000000100, __s13@0000000000000011)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7;
    info.eval->multiply_plain(ss[15], bits["1000000000000000"], t6_1);
    info.eval->multiply_plain(ss[16], bits["0010000000000000"], t6_2);
    info.eval->multiply_plain(ss[10], bits["0000010000000000"], t6_3);
    info.eval->multiply_plain(ss[19], bits["0000001100000000"], t6_4);
    info.eval->multiply_plain(ss[22], bits["0000000000010000"], t6_5);
    info.eval->multiply_plain(ss[20], bits["0000000000000100"], t6_6);
    info.eval->multiply_plain(ss[13], bits["0000000000000011"], t6_7);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7}, ts[6]);
    
    
    // __t7 = blend(__v0@1000011000010100, __s3@0010000100000011)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[0], bits["1000011000010100"], t7_1);
    info.eval->multiply_plain(ss[3], bits["0010000100000011"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s21@1000000000000001, __s18@0010000000000000, __s24@0000010000000000, __v1@0000001100000000, __s12@0000000000010000, __s23@0000000000000110)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6;
    info.eval->multiply_plain(ss[21], bits["1000000000000001"], t8_1);
    info.eval->multiply_plain(ss[18], bits["0010000000000000"], t8_2);
    info.eval->multiply_plain(ss[24], bits["0000010000000000"], t8_3);
    info.eval->multiply_plain(vs[1], bits["0000001100000000"], t8_4);
    info.eval->multiply_plain(ss[12], bits["0000000000010000"], t8_5);
    info.eval->multiply_plain(ss[23], bits["0000000000000110"], t8_6);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6}, ts[8]);
    
    
    // __t9 = blend(__s3@1000011000000100, __v0@0010000000000001, __s0@0000000100000000, __s7@0000000000010000, __s2@0000000000000010)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5;
    info.eval->multiply_plain(ss[3], bits["1000011000000100"], t9_1);
    info.eval->multiply_plain(vs[0], bits["0010000000000001"], t9_2);
    info.eval->multiply_plain(ss[0], bits["0000000100000000"], t9_3);
    info.eval->multiply_plain(ss[7], bits["0000000000010000"], t9_4);
    info.eval->multiply_plain(ss[2], bits["0000000000000010"], t9_5);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v4@1000010100010010, __v2@0010001000000000, __v3@0000000000000101)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[4], bits["1000010100010010"], t10_1);
    info.eval->multiply_plain(vs[2], bits["0010001000000000"], t10_2);
    info.eval->multiply_plain(vs[3], bits["0000000000000101"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v2@1000010000000000, __v3@0010000100010010, __v4@0000001000000101)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[2], bits["1000010000000000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["0010000100010010"], t11_2);
    info.eval->multiply_plain(vs[4], bits["0000001000000101"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->add(ts[00], ts[01], vs[5]); // __v5 = __t00 + __t01
    
    // __t12 = blend(__s17@1010000000000000, __v1@0000010000000000, __s11@0000001000000000, __s10@0000000100000000, __s20@0000000000010000, __s13@0000000000000100, __s21@0000000000000010, __s14@0000000000000001)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5, t12_6, t12_7, t12_8;
    info.eval->multiply_plain(ss[17], bits["1010000000000000"], t12_1);
    info.eval->multiply_plain(vs[1], bits["0000010000000000"], t12_2);
    info.eval->multiply_plain(ss[11], bits["0000001000000000"], t12_3);
    info.eval->multiply_plain(ss[10], bits["0000000100000000"], t12_4);
    info.eval->multiply_plain(ss[20], bits["0000000000010000"], t12_5);
    info.eval->multiply_plain(ss[13], bits["0000000000000100"], t12_6);
    info.eval->multiply_plain(ss[21], bits["0000000000000010"], t12_7);
    info.eval->multiply_plain(ss[14], bits["0000000000000001"], t12_8);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5, t12_6, t12_7, t12_8}, ts[12]);
    
    
    // __t13 = blend(__s4@1010000000000000, __s6@0000010000010001, __s7@0000001000000000, __v0@0000000100000000, __s0@0000000000000100, __s5@0000000000000010)
    ctxt t13_1, t13_2, t13_3, t13_4, t13_5, t13_6;
    info.eval->multiply_plain(ss[4], bits["1010000000000000"], t13_1);
    info.eval->multiply_plain(ss[6], bits["0000010000010001"], t13_2);
    info.eval->multiply_plain(ss[7], bits["0000001000000000"], t13_3);
    info.eval->multiply_plain(vs[0], bits["0000000100000000"], t13_4);
    info.eval->multiply_plain(ss[0], bits["0000000000000100"], t13_5);
    info.eval->multiply_plain(ss[5], bits["0000000000000010"], t13_6);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4, t13_5, t13_6}, ts[13]);
    
    info.eval->multiply(ts[02], ts[03], vs[6]); // __v6 = __t02 * __t03
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__v6@1000001000000000, __v4@0010000000000000, __v3@0000010000000000, __v2@0000000100010111)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(vs[6], bits["1000001000000000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["0010000000000000"], t14_2);
    info.eval->multiply_plain(vs[3], bits["0000010000000000"], t14_3);
    info.eval->multiply_plain(vs[2], bits["0000000100010111"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    info.eval->add(vs[5], ts[04], vs[7]); // __v7 = __v5 + __t04
    
    // __t15 = blend(__v3@1000001000000000, __v6@0010010100010111)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[3], bits["1000001000000000"], t15_1);
    info.eval->multiply_plain(vs[6], bits["0010010100010111"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->add(vs[7], ts[05], vs[8]); // __v8 = __v7 + __t05
    return vs[8];
}
    