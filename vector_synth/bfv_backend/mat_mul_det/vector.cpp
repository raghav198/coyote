
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0111", info);
    add_bitstring(bits, "1001", info);
    add_bitstring(bits, "1100", info);
    add_bitstring(bits, "0001", info);
    add_bitstring(bits, "0010", info);
    add_bitstring(bits, "0100", info);
    add_bitstring(bits, "0101", info);
    add_bitstring(bits, "1101", info);
    add_bitstring(bits, "1000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("11110110111101011111", info);
    ts[1] = encrypt_input("11110110111101011111", info);
    ts[2] = encrypt_input("11010111111101111110", info);
    ts[3] = encrypt_input("11010111111101111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[8];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -3, gk, ss[3]); // __s3 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -2, gk, ss[4]); // __s4 = __v1 >> 2
    
    // __t4 = blend(__s0@1101, __v0@0010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[0], bits["1101"], t4_1);
    info.eval->multiply_plain(vs[0], bits["0010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s3@1001, __s2@0100, __v1@0010)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[3], bits["1001"], t5_1);
    info.eval->multiply_plain(ss[2], bits["0100"], t5_2);
    info.eval->multiply_plain(vs[1], bits["0010"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__v0@1000, __s1@0101, __s0@0010)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[0], bits["1000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["0101"], t6_2);
    info.eval->multiply_plain(ss[0], bits["0010"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s4@1100, __s2@0010, __v1@0001)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(ss[4], bits["1100"], t7_1);
    info.eval->multiply_plain(ss[2], bits["0010"], t7_2);
    info.eval->multiply_plain(vs[1], bits["0001"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__v3@1000, __v2@0111)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["1000"], t8_1);
    info.eval->multiply_plain(vs[2], bits["0111"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v2@1000, __v3@0111)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["1000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["0111"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -2, gk, ss[5]); // __s5 = __v4 >> 2
    info.eval->rotate_rows(vs[4], -1, gk, ss[6]); // __s6 = __v4 >> 1
    info.eval->rotate_rows(vs[4], -3, gk, ss[7]); // __s7 = __v4 >> 3
    info.eval->multiply(ss[6], vs[4], vs[5]); // __v5 = __s6 * __v4
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->multiply(ss[7], ss[5], vs[6]); // __v6 = __s7 * __s5
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[6], vs[5], vs[7]); // __v7 = __v6 + __v5
    return vs[7];
}
    