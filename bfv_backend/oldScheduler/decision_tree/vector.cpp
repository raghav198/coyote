
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "000000010", info);
    add_bitstring(bits, "000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(9);
    ts[0] = encrypt_input("001110011", info);
    ts[1] = encrypt_input("0011111111111111111111111111111111111111111111111111111100111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("11111111111111111111111111111111111100011111111111111111111111111111111111100", info);
    ts[3] = encrypt_input("111111111111111111111111111111111111110001111111111111111111111111111111111111100", info);
    ts[4] = encrypt_input("000111111111111111111100011111111111111111110", info);
    ts[7] = encrypt_input("00000000111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[5];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -3, gk, ss[1]); // __s1 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    
    // __t5 = blend(__s0@000100000, __v0@000000010)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[0], bits["000100000"], t5_1);
    info.eval->multiply_plain(vs[0], bits["000000010"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[5], ts[4], vs[2]); // __v2 = __t5 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s1@000100000, __s2@000000010)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[1], bits["000100000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["000000010"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(ts[6], vs[2], vs[3]); // __v3 = __t6 + __v2
    info.eval->rotate_rows(vs[3], -1, gk, ss[3]); // __s3 = __v3 >> 1
    info.eval->multiply(vs[0], ss[3], vs[4]); // __v4 = __v0 * __s3
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->add(ss[1], vs[4], vs[5]); // __v5 = __s1 + __v4
    
    // __t8 = blend(__s0@000010000, __t7@000000001)
    ctxt t8_1;
    info.eval->multiply_plain(ss[0], bits["000010000"], t8_1);
    info.eval->add(t8_1, ts[7], ts[8]);
    
    info.eval->multiply(ts[8], vs[5], vs[6]); // __v6 = __t8 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -5, gk, ss[4]); // __s4 = __v6 >> 5
    info.eval->add(ss[4], vs[6], vs[7]); // __v7 = __s4 + __v6
    return vs[7];
}
    