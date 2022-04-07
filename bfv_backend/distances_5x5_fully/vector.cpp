
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000000001100100110101000000011000010100", info);
    add_bitstring(bits, "000000000000001000000010101000000000000010100", info);
    add_bitstring(bits, "000000000000000100100100000000000011000000000", info);
    add_bitstring(bits, "000000000000000010000000000000000000101000000", info);
    add_bitstring(bits, "100000010000000000011000000010000000000000000", info);
    add_bitstring(bits, "000000000001000000000000010000111000000000001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(8);
    ts[0] = encrypt_input("000000000000001111111111111111111111111000111111111111111111111111111111111111111111111111110111111111111111111111111001111111111111111111111111000000000000000000000", info);
    ts[2] = encrypt_input("001111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111110111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111110111111111111111111111111001111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111110011111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[9];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->sub(vs[0], vs[1], vs[2]); // __v2 = __v0 - __v1
    info.eval->rotate_rows(vs[2], -18, gk, ss[0]); // __s0 = __v2 >> 18
    info.eval->rotate_rows(vs[2], -7, gk, ss[1]); // __s1 = __v2 >> 7
    info.eval->rotate_rows(vs[2], -44, gk, ss[2]); // __s2 = __v2 >> 44
    info.eval->rotate_rows(vs[2], -36, gk, ss[3]); // __s3 = __v2 >> 36
    info.eval->rotate_rows(vs[2], -40, gk, ss[4]); // __s4 = __v2 >> 40
    info.eval->rotate_rows(vs[2], -38, gk, ss[5]); // __s5 = __v2 >> 38
    info.eval->rotate_rows(vs[2], -28, gk, ss[6]); // __s6 = __v2 >> 28
    info.eval->rotate_rows(vs[2], -32, gk, ss[7]); // __s7 = __v2 >> 32
    info.eval->rotate_rows(vs[2], -24, gk, ss[8]); // __s8 = __v2 >> 24
    
    // __t4 = blend(__v2@100000010000000000011000000010000000000000000, __v2@000000000001000000000000010000111000000000001)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[2], bits["100000010000000000011000000010000000000000000"], t4_1);
    info.eval->multiply_plain(vs[2], bits["000000000001000000000000010000111000000000001"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(ts[4], ts[4], vs[4]); // __v4 = __t4 * __t4
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t6 = blend(__v2@000000000000001100100110101000000011000010100, __v2@000000000000000010000000000000000000101000000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[2], bits["000000000000001100100110101000000011000010100"], t6_1);
    info.eval->multiply_plain(vs[2], bits["000000000000000010000000000000000000101000000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__v2@000000000000001000000010101000000000000010100, __v2@000000000000000100100100000000000011000000000, __v2@000000000000000010000000000000000000101000000)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[2], bits["000000000000001000000010101000000000000010100"], t7_1);
    info.eval->multiply_plain(vs[2], bits["000000000000000100100100000000000011000000000"], t7_2);
    info.eval->multiply_plain(vs[2], bits["000000000000000010000000000000000000101000000"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[6]); // __v6 = __t6 * __t7
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    