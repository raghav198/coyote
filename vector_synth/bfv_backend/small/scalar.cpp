
#include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 31;
}

std::vector<ctxt> ScalarProgram::computation(std::map<char, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs['q'], locs['u'], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs['u'], regs[0], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(locs['v'], locs['o'], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(regs[2], locs['v'], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[1], regs[3], regs[4]);
    info.eval->multiply(locs['x'], locs['i'], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs['v'], locs['b'], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(regs[5], regs[6], regs[7]);
    info.eval->add(locs['j'], regs[7], regs[8]);
    info.eval->multiply(regs[4], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs['l'], locs['k'], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(locs['k'], locs['q'], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(locs['m'], locs['d'], regs[13]);
    info.eval->multiply(regs[12], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs['d'], locs['c'], regs[15]);
    info.eval->multiply(locs['u'], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[14], regs[16], regs[17]);
    info.eval->add(locs['i'], locs['g'], regs[18]);
    info.eval->multiply(locs['t'], locs['l'], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->multiply(locs['a'], locs['m'], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs['r'], locs['x'], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs['v'], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[21], regs[23], regs[24]);
    info.eval->add(locs['p'], locs['p'], regs[25]);
    info.eval->multiply(regs[25], locs['c'], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(locs['i'], locs['q'], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[27], locs['p'], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[26], regs[28], regs[29]);
    info.eval->multiply(regs[24], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[9]);
    answer.push_back(regs[17]);
    answer.push_back(regs[20]);
    answer.push_back(regs[30]);
    return answer;
}
    