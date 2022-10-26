
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "010111010", info);
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "000111000", info);
    add_bitstring(bits, "100100000", info);
    add_bitstring(bits, "000000111", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "001000101", info);
    add_bitstring(bits, "111000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(9);
    ts[0] = encrypt_input("0111111111111111111011111111111111111111111111111111111011111111111111111101111111111111111110", info);
    ts[1] = encrypt_input("0111111111111111111011111111111111111111111111111111111011111111111111111101111111111111111110", info);
    ts[2] = encrypt_input("000111111111111111111111111111111111110111111111111111111000", info);
    ts[3] = encrypt_input("000111111111111111111111111111111111110111111111111111111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[7];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -3, gk, ss[2]); // __s2 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -6, gk, ss[3]); // __s3 = __v1 >> 6
    
    // __t4 = blend(__s1@100000000, __v0@010111010, __s0@001000101)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[1], bits["100000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["010111010"], t4_2);
    info.eval->multiply_plain(ss[0], bits["001000101"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__s3@111000000, __v1@000111000, __s2@000000111)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[3], bits["111000000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["000111000"], t5_2);
    info.eval->multiply_plain(ss[2], bits["000000111"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -3, gk, ss[4]); // __s4 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -7, gk, ss[5]); // __s5 = __v2 >> 7
    info.eval->rotate_rows(vs[2], -5, gk, ss[6]); // __s6 = __v2 >> 5
    
    // __t6 = blend(__s5@100100000, __s6@000010000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[5], bits["100100000"], t6_1);
    info.eval->multiply_plain(ss[6], bits["000010000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__v2@100100000, __s5@000010000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[2], bits["100100000"], t7_1);
    info.eval->multiply_plain(ss[5], bits["000010000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[3]); // __v3 = __t6 + __t7
    
    // __t8 = blend(__s6@100100000, __s4@000010000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[6], bits["100100000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["000010000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    info.eval->add(ts[8], vs[3], vs[4]); // __v4 = __t8 + __v3
    return vs[4];
}
    