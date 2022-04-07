
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "001100", info);
    add_bitstring(bits, "110000", info);
    add_bitstring(bits, "100110", info);
    add_bitstring(bits, "101000", info);
    add_bitstring(bits, "010000", info);
    add_bitstring(bits, "000011", info);
    add_bitstring(bits, "011001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(8);
    ts[0] = encrypt_input("01111111111111111111111111111111111100111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("01111111111111111111111111111111111100111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("0011111111111111111011111111111111111100", info);
    ts[3] = encrypt_input("0011111111111111111011111111111111111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -5, gk, ss[0]); // __s0 = __v0 >> 5
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -2, gk, ss[1]); // __s1 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -4, gk, ss[2]); // __s2 = __v1 >> 4
    
    // __t4 = blend(__s0@100110, __v0@011001)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[0], bits["100110"], t4_1);
    info.eval->multiply_plain(vs[0], bits["011001"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s2@110000, __v1@001100, __s1@000011)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[2], bits["110000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["001100"], t5_2);
    info.eval->multiply_plain(ss[1], bits["000011"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -3, gk, ss[3]); // __s3 = __v2 >> 3
    
    // __t6 = blend(__v2@101000, __s3@010000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[2], bits["101000"], t6_1);
    info.eval->multiply_plain(ss[3], bits["010000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__s3@101000, __v2@010000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[3], bits["101000"], t7_1);
    info.eval->multiply_plain(vs[2], bits["010000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[3]); // __v3 = __t6 + __t7
    return vs[3];
}
    