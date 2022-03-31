
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000001000000000000", info);
    add_bitstring(bits, "000000010001000000", info);
    add_bitstring(bits, "000001010000000000", info);
    add_bitstring(bits, "000000100000000000", info);
    add_bitstring(bits, "000000011010000000", info);
    add_bitstring(bits, "001000000000000000", info);
    add_bitstring(bits, "000000000100011011", info);
    add_bitstring(bits, "000000010000000000", info);
    add_bitstring(bits, "000000000000000010", info);
    add_bitstring(bits, "000000000000000001", info);
    add_bitstring(bits, "000000001000000000", info);
    add_bitstring(bits, "000000000000011011", info);
    add_bitstring(bits, "000000000010000000", info);
    add_bitstring(bits, "000000000001010011", info);
    add_bitstring(bits, "000000100000000001", info);
    add_bitstring(bits, "000000000001000010", info);
    add_bitstring(bits, "000000000100000000", info);
    add_bitstring(bits, "001000100000000000", info);
    add_bitstring(bits, "000000000000010001", info);
    add_bitstring(bits, "000001000001010011", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(18);
    ts[0] = encrypt_input("001110001100011011100111111111111110", info);
    ts[1] = encrypt_input("001110001110011111100111110111110111", info);
    ts[2] = encrypt_input("011111100111011000001111111110111110", info);
    ts[3] = encrypt_input("011111100111011000001111111100110111", info);
    ts[4] = encrypt_input("00011000110110111110111111011100111110", info);
    ts[5] = encrypt_input("00011000111110111111111110011100110111", info);
    ts[8] = encrypt_input("1100001111110011100111011100111110", info);
    ts[9] = encrypt_input("1100001111110011100110011100110111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[11];

    info.eval->sub(ts[0], ts[1], vs[0]); // __v0 = __t0 - __t1
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->sub(ts[2], ts[3], vs[1]); // __v1 = __t2 - __t3
    info.eval->rotate_rows(vs[1], -5, gk, ss[1]); // __s1 = __v1 >> 5
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    info.eval->rotate_rows(vs[2], -2, gk, ss[2]); // __s2 = __v2 >> 2
    
    // __t6 = blend(__v1@001000000000000000, __v2@000000100000000000, __v0@000000000100011011)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[1], bits["001000000000000000"], t6_1);
    info.eval->multiply_plain(vs[2], bits["000000100000000000"], t6_2);
    info.eval->multiply_plain(vs[0], bits["000000000100011011"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__v0@001000100000000000, __v2@000000000100000000, __v1@000000000000011011)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[0], bits["001000100000000000"], t7_1);
    info.eval->multiply_plain(vs[2], bits["000000000100000000"], t7_2);
    info.eval->multiply_plain(vs[1], bits["000000000000011011"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -5, gk, ss[3]); // __s3 = __v3 >> 5
    info.eval->rotate_rows(vs[3], -2, gk, ss[4]); // __s4 = __v3 >> 2
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    info.eval->rotate_rows(vs[4], -5, gk, ss[5]); // __s5 = __v4 >> 5
    info.eval->rotate_rows(vs[4], -2, gk, ss[6]); // __s6 = __v4 >> 2
    
    // __t10 = blend(__v4@000001000001010011, __v2@000000011010000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[4], bits["000001000001010011"], t10_1);
    info.eval->multiply_plain(vs[2], bits["000000011010000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v1@000001010000000000, __v4@000000001000000000, __v0@000000000010000000, __v2@000000000001010011)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(vs[1], bits["000001010000000000"], t11_1);
    info.eval->multiply_plain(vs[4], bits["000000001000000000"], t11_2);
    info.eval->multiply_plain(vs[0], bits["000000000010000000"], t11_3);
    info.eval->multiply_plain(vs[2], bits["000000000001010011"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -2, gk, ss[7]); // __s7 = __v5 >> 2
    info.eval->rotate_rows(vs[5], -5, gk, ss[8]); // __s8 = __v5 >> 5
    info.eval->rotate_rows(vs[5], -7, gk, ss[9]); // __s9 = __v5 >> 7
    
    // __t12 = blend(__v5@000000000000010001, __v3@000000000000000010)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["000000000000010001"], t12_1);
    info.eval->multiply_plain(vs[3], bits["000000000000000010"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v3@000000000000010001, __v5@000000000000000010)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[3], bits["000000000000010001"], t13_1);
    info.eval->multiply_plain(vs[5], bits["000000000000000010"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    
    // __t14 = blend(__s5@000001000000000000, __s1@000000100000000001)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[5], bits["000001000000000000"], t14_1);
    info.eval->multiply_plain(ss[1], bits["000000100000000001"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__s2@000001000000000000, __s6@000000100000000000, __s0@000000000000000001)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(ss[2], bits["000001000000000000"], t15_1);
    info.eval->multiply_plain(ss[6], bits["000000100000000000"], t15_2);
    info.eval->multiply_plain(ss[0], bits["000000000000000001"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -7, gk, ss[10]); // __s10 = __v7 >> 7
    
    // __t16 = blend(__s3@000000010001000000, __s8@000000000000000010, __v7@000000000000000001)
    ctxt t16_1, t16_2, t16_3;
    info.eval->multiply_plain(ss[3], bits["000000010001000000"], t16_1);
    info.eval->multiply_plain(ss[8], bits["000000000000000010"], t16_2);
    info.eval->multiply_plain(vs[7], bits["000000000000000001"], t16_3);
    info.eval->add_many({t16_1, t16_2, t16_3}, ts[16]);
    
    
    // __t17 = blend(__s7@000000010000000000, __s4@000000000001000010, __s9@000000000000000001)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(ss[7], bits["000000010000000000"], t17_1);
    info.eval->multiply_plain(ss[4], bits["000000000001000010"], t17_2);
    info.eval->multiply_plain(ss[9], bits["000000000000000001"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3}, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[8]); // __v8 = __t16 + __t17
    info.eval->add(ss[8], ss[10], vs[9]); // __v9 = __s8 + __s10
    return vs[9];
}
    