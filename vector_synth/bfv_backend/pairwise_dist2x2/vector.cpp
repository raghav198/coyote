
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "010100010", info);
    add_bitstring(bits, "000001101", info);
    add_bitstring(bits, "011110010", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "000000101", info);
    add_bitstring(bits, "001010000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("0110110110110111111111111", info);
    ts[1] = encrypt_input("0110110110110111111111111", info);
    ts[2] = encrypt_input("1101101101101111111111110", info);
    ts[3] = encrypt_input("1101101101101111111111110", info);
    ts[4] = encrypt_input("0110110111111110110111111", info);
    ts[5] = encrypt_input("0110110111111110110111111", info);
    ts[6] = encrypt_input("1101101111111101101111110", info);
    ts[7] = encrypt_input("1101101111111101101111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[5];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[1]); // __s1 = __v1 >> 1
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -1, gk, ss[2]); // __s2 = __v2 >> 1
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -1, gk, ss[3]); // __s3 = __v3 >> 1
    
    // __t8 = blend(__v1@010100010, __v0@001010000, __s1@000001000, __s0@000000101)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[1], bits["010100010"], t8_1);
    info.eval->multiply_plain(vs[0], bits["001010000"], t8_2);
    info.eval->multiply_plain(ss[1], bits["000001000"], t8_3);
    info.eval->multiply_plain(ss[0], bits["000000101"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__v3@010100010, __v2@001010000, __s3@000001000, __s2@000000101)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(vs[3], bits["010100010"], t9_1);
    info.eval->multiply_plain(vs[2], bits["001010000"], t9_2);
    info.eval->multiply_plain(ss[3], bits["000001000"], t9_3);
    info.eval->multiply_plain(ss[2], bits["000000101"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__s1@010100010, __s0@001010000, __v1@000001000, __v0@000000101)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[1], bits["010100010"], t10_1);
    info.eval->multiply_plain(ss[0], bits["001010000"], t10_2);
    info.eval->multiply_plain(vs[1], bits["000001000"], t10_3);
    info.eval->multiply_plain(vs[0], bits["000000101"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s3@010100010, __s2@001010000, __v3@000001000, __v2@000000101)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[3], bits["010100010"], t11_1);
    info.eval->multiply_plain(ss[2], bits["001010000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["000001000"], t11_3);
    info.eval->multiply_plain(vs[2], bits["000000101"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v4@011110010, __v5@000001101)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[4], bits["011110010"], t12_1);
    info.eval->multiply_plain(vs[5], bits["000001101"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v5@011110010, __v4@000001101)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[5], bits["011110010"], t13_1);
    info.eval->multiply_plain(vs[4], bits["000001101"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -1, gk, ss[4]); // __s4 = __v6 >> 1
    info.eval->add(vs[6], ss[4], vs[7]); // __v7 = __v6 + __s4
    info.eval->add(vs[6], ss[4], vs[8]); // __v8 = __v6 + __s4
    info.eval->add(vs[6], ss[4], vs[9]); // __v9 = __v6 + __s4
    info.eval->add(vs[6], ss[4], vs[10]); // __v10 = __v6 + __s4
    return vs[10];
}
    