
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100100000001100000000000000000000", info);
    add_bitstring(bits, "110100000001100000000000000000000", info);
    add_bitstring(bits, "011000000000000000000000000000000", info);
    add_bitstring(bits, "001000000000000000000000000000000", info);
    add_bitstring(bits, "010010000010000000000000000000000", info);
    add_bitstring(bits, "101100000001101000000000000000000", info);
    add_bitstring(bits, "010000000000000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(15);
    ts[0] = encrypt_input("111111101111110111110000000110111101111111110111111111111011110110101111111110001101111011000110101101000", info);
    ts[1] = encrypt_input("111111101111110111110000000110111101111111110111111111111011110110101111111110001101111011000110101101000", info);
    ts[2] = encrypt_input("000000000000011111111101111011111111101101111010110101101111010111111111111111011111110111101111011011011", info);
    ts[3] = encrypt_input("000000000000011111111101111011111111101101111010110101101111010111111111111111011111110111101111011011011", info);
    ts[4] = encrypt_input("000011111000001111100011110000000000000000000", info);
    ts[7] = encrypt_input("000011110000001111000011111000000000000000000", info);
    ts[12] = encrypt_input("000011111000001111100011111000000000000000000", info);
    ts[13] = encrypt_input("111111111011110111111111000000111111111111111011111000000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -20, gk, ss[0]); // __s0 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -15, gk, ss[1]); // __s1 = __v0 >> 15
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -20, gk, ss[2]); // __s2 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -15, gk, ss[3]); // __s3 = __v1 >> 15
    
    // __t5 = blend(__s1@100100000001100000000000000000000, __s0@010000000000000000000000000000000, __v0@001000000000000000000000000000000, __t4@000010000010001000000000000000000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[1], bits["100100000001100000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[0], bits["010000000000000000000000000000000"], t5_2);
    info.eval->multiply_plain(vs[0], bits["001000000000000000000000000000000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3, ts[4]}, ts[5]);
    
    
    // __t6 = blend(__s3@101100000001101000000000000000000, __s2@010010000010000000000000000000000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[3], bits["101100000001101000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["010010000010000000000000000000000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->multiply(ts[5], ts[6], vs[2]); // __v2 = __t5 * __t6
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t8 = blend(__s0@100100000001100000000000000000000, __s1@011000000000000000000000000000000, __t7@000010000010001000000000000000000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[0], bits["100100000001100000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["011000000000000000000000000000000"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[7]}, ts[8]);
    
    
    // __t9 = blend(__s2@101100000001101000000000000000000, __s3@010010000010000000000000000000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[2], bits["101100000001101000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[3], bits["010010000010000000000000000000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t10 = blend(__v2@101100000001101000000000000000000, __v3@010010000010000000000000000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[2], bits["101100000001101000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["010010000010000000000000000000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v3@101100000001101000000000000000000, __v2@010010000010000000000000000000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[3], bits["101100000001101000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[2], bits["010010000010000000000000000000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[4]); // __v4 = __t10 + __t11
    
    // __t14 = blend(__v0@110100000001100000000000000000000, __s0@001000000000000000000000000000000, __t12@000010000010001000000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[0], bits["110100000001100000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[0], bits["001000000000000000000000000000000"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[12]}, ts[14]);
    
    info.eval->multiply(ts[14], ts[13], vs[5]); // __v5 = __t14 * __t13
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->add(vs[4], vs[5], vs[6]); // __v6 = __v4 + __v5
    return vs[6];
}
    