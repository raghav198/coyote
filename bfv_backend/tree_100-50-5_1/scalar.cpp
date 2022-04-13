
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"475", "907", "17", "966", "864", "644", "563", "24"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["24"], locs["644"], regs[0]);
    info.eval->add(regs[0], locs["17"], regs[1]);
    info.eval->add(locs["563"], regs[1], regs[2]);
    info.eval->add(locs["864"], regs[2], regs[3]);
    info.eval->multiply(locs["907"], locs["966"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[4], locs["475"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[3], regs[5], regs[6]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    