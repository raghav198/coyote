
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "001000000000000011000000000000", info);
    add_bitstring(bits, "000000000110000001000000110000", info);
    add_bitstring(bits, "000000000110000001000000010000", info);
    add_bitstring(bits, "001000000000000001000000000000", info);
    add_bitstring(bits, "001000000110000010000010010000", info);
    add_bitstring(bits, "001000000000000101000000000000", info);
    add_bitstring(bits, "100000001000000100000001000000", info);
    add_bitstring(bits, "000001000000000000001000100000", info);
    add_bitstring(bits, "000000010000000001000000000000", info);
    add_bitstring(bits, "100000001110000010000011010000", info);
    add_bitstring(bits, "010000000000000010000000000000", info);
    add_bitstring(bits, "000000000000000010000000000000", info);
    add_bitstring(bits, "010000000000000000000000000000", info);
    add_bitstring(bits, "000000010000000000000000000000", info);
    add_bitstring(bits, "001000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("0111111001110000011100010111111001111010011100000", info);
    ts[1] = encrypt_input("0111100011100000111000111111111001111110011100000", info);
    ts[2] = encrypt_input("0101000111111011100001100001110010111100001100011100", info);
    ts[3] = encrypt_input("0111001111110110000011100011100111111000111001100", info);
    ts[4] = encrypt_input("11100000111011110111001111110000000101111011111100111", info);
    ts[5] = encrypt_input("11100000111011111111100110110000000011111011111100111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[7];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -26, gk, ss[0]); // __s0 = __v0 >> 26
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -26, gk, ss[1]); // __s1 = __v1 >> 26
    
    // __t6 = blend(__v1@010000000000000010000000000000, __v0@000001000000000000001000100000, __t4@100000101110011000000011011001)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[1], bits["010000000000000010000000000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["000001000000000000001000100000"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v0@010000000000000010000000000000, __v1@000001000000000000001000100000, __t5@100000101110011000000011011001)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[0], bits["010000000000000010000000000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["000001000000000000001000100000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -26, gk, ss[2]); // __s2 = __v2 >> 26
    
    // __t8 = blend(__v2@100000001110000010000011010000, __s2@010000000000000000000000000000, __v0@001000000000000101000000000000, __v1@000000010000000000000000000000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[2], bits["100000001110000010000011010000"], t8_1);
    info.eval->multiply_plain(ss[2], bits["010000000000000000000000000000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["001000000000000101000000000000"], t8_3);
    info.eval->multiply_plain(vs[1], bits["000000010000000000000000000000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s1@100000001000000100000001000000, __v2@010000000000000000000000000000, __s2@001000000110000010000010010000, __s0@000000010000000001000000000000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[1], bits["100000001000000100000001000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["010000000000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[2], bits["001000000110000010000010010000"], t9_3);
    info.eval->multiply_plain(ss[0], bits["000000010000000001000000000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -2, gk, ss[3]); // __s3 = __v3 >> 2
    
    // __t10 = blend(__s3@001000000000000000000000000000, __v3@000000000110000001000000010000, __v2@000000000000000000000000100000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[3], bits["001000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["000000000110000001000000010000"], t10_2);
    info.eval->multiply_plain(vs[2], bits["000000000000000000000000100000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v3@001000000000000000000000000000, __s3@000000000110000001000000110000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[3], bits["001000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[3], bits["000000000110000001000000110000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -22, gk, ss[4]); // __s4 = __v4 >> 22
    
    // __t12 = blend(__s4@010000000000000000000000000000, __v4@001000000000000001000000000000, __v3@000000000000000010000000000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[4], bits["010000000000000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["001000000000000001000000000000"], t12_2);
    info.eval->multiply_plain(vs[3], bits["000000000000000010000000000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__v3@010000000000000000000000000000, __s4@001000000000000011000000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[3], bits["010000000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[4], bits["001000000000000011000000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[5]); // __v5 = __t12 * __t13
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -15, gk, ss[5]); // __s5 = __v5 >> 15
    info.eval->multiply(vs[5], ss[5], vs[6]); // __v6 = __v5 * __s5
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -29, gk, ss[6]); // __s6 = __v6 >> 29
    info.eval->multiply(vs[6], ss[6], vs[7]); // __v7 = __v6 * __s6
    info.eval->relinearize_inplace(vs[7], rk);
    return vs[7];
}
    