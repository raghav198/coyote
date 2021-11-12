
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100000001", info);
    add_bitstring(bits, "000000011", info);
    add_bitstring(bits, "010000000", info);
    add_bitstring(bits, "110000000", info);
    add_bitstring(bits, "000111011", info);
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "001000000", info);
    add_bitstring(bits, "100000010", info);
    add_bitstring(bits, "001000011", info);
    add_bitstring(bits, "010000001", info);
    add_bitstring(bits, "000111100", info);
    add_bitstring(bits, "001111000", info);
    add_bitstring(bits, "001000100", info);
    add_bitstring(bits, "111000000", info);
    add_bitstring(bits, "110111000", info);
    add_bitstring(bits, "000000010", info);
    add_bitstring(bits, "000000001", info);
    add_bitstring(bits, "110000100", info);
    add_bitstring(bits, "000000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(19);
    ts[0] = encrypt_input("111100110111111111010110111111100", info);
    ts[1] = encrypt_input("111100110111111111010110111111100", info);
    ts[2] = encrypt_input("000110111101111010111111111111110", info);
    ts[3] = encrypt_input("000110111101111010111111111111110", info);
    ts[4] = encrypt_input("000111111111111111000", info);
    ts[5] = encrypt_input("0001111111111111101111100", info);
    ts[8] = encrypt_input("000111101111011110000", info);
    ts[9] = encrypt_input("111111111111110000000", info);
    ts[12] = encrypt_input("000111111111111111000", info);
    ts[13] = encrypt_input("00000001111011111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[14];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -4, gk, ss[2]); // __s2 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -5, gk, ss[3]); // __s3 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -6, gk, ss[4]); // __s4 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -8, gk, ss[5]); // __s5 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -7, gk, ss[6]); // __s6 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -3, gk, ss[7]); // __s7 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -3, gk, ss[8]); // __s8 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -6, gk, ss[9]); // __s9 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -4, gk, ss[10]); // __s10 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -2, gk, ss[11]); // __s11 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -1, gk, ss[12]); // __s12 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -8, gk, ss[13]); // __s13 = __v1 >> 8
    
    // __t6 = blend(__v0@100000000, __s0@010000000, __s5@001000000, __s2@000000100, __s1@000000010, __s7@000000001, __t4@000111000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(vs[0], bits["100000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["010000000"], t6_2);
    info.eval->multiply_plain(ss[5], bits["001000000"], t6_3);
    info.eval->multiply_plain(ss[2], bits["000000100"], t6_4);
    info.eval->multiply_plain(ss[1], bits["000000010"], t6_5);
    info.eval->multiply_plain(ss[7], bits["000000001"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__s9@110000000, __s8@001000000, __s13@000000010, __s12@000000001, __t5@000111100)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[9], bits["110000000"], t7_1);
    info.eval->multiply_plain(ss[8], bits["001000000"], t7_2);
    info.eval->multiply_plain(ss[13], bits["000000010"], t7_3);
    info.eval->multiply_plain(ss[12], bits["000000001"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t10 = blend(__s7@100000010, __s2@010000001, __s3@001000000, __s0@000000100, __t8@000111000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[7], bits["100000010"], t10_1);
    info.eval->multiply_plain(ss[2], bits["010000001"], t10_2);
    info.eval->multiply_plain(ss[3], bits["001000000"], t10_3);
    info.eval->multiply_plain(ss[0], bits["000000100"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__v1@000111100, __s11@000000010, __s10@000000001, __t9@111000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[1], bits["000111100"], t11_1);
    info.eval->multiply_plain(ss[11], bits["000000010"], t11_2);
    info.eval->multiply_plain(ss[10], bits["000000001"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t14 = blend(__s4@100000001, __s6@010000000, __s1@001000100, __s3@000000010, __t12@000111000)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(ss[4], bits["100000001"], t14_1);
    info.eval->multiply_plain(ss[6], bits["010000000"], t14_2);
    info.eval->multiply_plain(ss[1], bits["001000100"], t14_3);
    info.eval->multiply_plain(ss[3], bits["000000010"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4, ts[12]}, ts[14]);
    
    
    // __t15 = blend(__s8@110000100, __s9@001111000, __t13@000000011)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[8], bits["110000100"], t15_1);
    info.eval->multiply_plain(ss[9], bits["001111000"], t15_2);
    info.eval->add_many({t15_1, t15_2, ts[13]}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[4]); // __v4 = __t14 * __t15
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t16 = blend(__v2@110000000, __v4@001000100, __v3@000111011)
    ctxt t16_1, t16_2, t16_3;
    info.eval->multiply_plain(vs[2], bits["110000000"], t16_1);
    info.eval->multiply_plain(vs[4], bits["001000100"], t16_2);
    info.eval->multiply_plain(vs[3], bits["000111011"], t16_3);
    info.eval->add_many({t16_1, t16_2, t16_3}, ts[16]);
    
    
    // __t17 = blend(__v4@110111000, __v2@001000011, __v3@000000100)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(vs[4], bits["110111000"], t17_1);
    info.eval->multiply_plain(vs[2], bits["001000011"], t17_2);
    info.eval->multiply_plain(vs[3], bits["000000100"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3}, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[5]); // __v5 = __t16 + __t17
    
    // __t18 = blend(__v3@111000000, __v2@000111100, __v4@000000011)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[3], bits["111000000"], t18_1);
    info.eval->multiply_plain(vs[2], bits["000111100"], t18_2);
    info.eval->multiply_plain(vs[4], bits["000000011"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    info.eval->add(vs[5], ts[18], vs[6]); // __v6 = __v5 + __t18
    return vs[6];
}
    