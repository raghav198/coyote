
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00100", info);
    add_bitstring(bits, "01000", info);
    add_bitstring(bits, "00001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1101110111111", info);
    ts[1] = encrypt_input("11111111111111", info);
    ts[2] = encrypt_input("0101000", info);
    ts[5] = encrypt_input("0001110", info);
    ts[6] = encrypt_input("0011100", info);
    ts[7] = encrypt_input("0101000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[4];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    
    // __t3 = blend(__v0@00001, __t2@01000)
    ctxt t3_1;
    info.eval->multiply_plain(vs[0], bits["00001"], t3_1);
    info.eval->add(t3_1, ts[2], ts[3]);
    
    
    // __t4 = blend(__v0@01000, __s0@00001)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[0], bits["01000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00001"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(ts[3], ts[4], vs[1]); // __v1 = __t3 * __t4
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -3, gk, ss[1]); // __s1 = __v1 >> 3
    info.eval->add(vs[0], ts[5], vs[2]); // __v2 = __v0 + __t5
    info.eval->rotate_rows(vs[2], -3, gk, ss[2]); // __s2 = __v2 >> 3
    info.eval->multiply(ss[1], ts[6], vs[3]); // __v3 = __s1 * __t6
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->add(vs[1], ss[2], vs[4]); // __v4 = __v1 + __s2
    
    // __t8 = blend(__v4@01000, __v3@00100)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[4], bits["01000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["00100"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v0@00100, __t7@01000)
    ctxt t9_1;
    info.eval->multiply_plain(vs[0], bits["00100"], t9_1);
    info.eval->add(t9_1, ts[7], ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[5]); // __v5 = __t8 * __t9
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -1, gk, ss[3]); // __s3 = __v5 >> 1
    info.eval->multiply(ss[3], vs[5], vs[6]); // __v6 = __s3 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    