
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 6;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"33", "702", "240", "9", "722", "180", "101"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["240"], locs["33"], regs[0]);
    info.eval->add(locs["180"], locs["101"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["9"], locs["722"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["702"], regs[3], regs[4]);
    info.eval->add(regs[2], regs[4], regs[5]);
    std::vector<ctxt> answer;
    answer.push_back(regs[5]);
    return answer;
}
    