
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000101000", info);
    add_bitstring(bits, "000110000", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "000100000", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "111100000", info);
    add_bitstring(bits, "000010111", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(8);
    ts[0] = encrypt_input("000011111111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("000011111111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111101111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    ts[3] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111101111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -8, gk, ss[1]); // __s1 = __v0 >> 8
    vs[1] = ts[2]; // vector load instr
    
    // __t4 = blend(__s0@111100000, __v0@000010111, __s1@000001000)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[0], bits["111100000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["000010111"], t4_2);
    info.eval->multiply_plain(ss[1], bits["000001000"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    info.eval->multiply(ts[4], vs[1], vs[2]); // __v2 = __t4 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -3, gk, ss[2]); // __s2 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -6, gk, ss[3]); // __s3 = __v2 >> 6
    
    // __t5 = blend(__v2@000101000, __s3@000010000)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[2], bits["000101000"], t5_1);
    info.eval->multiply_plain(ss[3], bits["000010000"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    
    // __t6 = blend(__s2@000110000, __s3@000001000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[2], bits["000110000"], t6_1);
    info.eval->multiply_plain(ss[3], bits["000001000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(ts[5], ts[6], vs[3]); // __v3 = __t5 + __t6
    info.eval->add(ss[2], vs[3], vs[4]); // __v4 = __s2 + __v3
    
    // __t7 = blend(__s3@000100000, __v2@000010000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[3], bits["000100000"], t7_1);
    info.eval->multiply_plain(vs[2], bits["000010000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->add(ts[7], vs[3], vs[5]); // __v5 = __t7 + __v3
    return vs[5];
}
    