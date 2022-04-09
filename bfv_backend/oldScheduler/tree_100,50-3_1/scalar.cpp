
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"781", "893", "508", "861", "30", "228", "1012", "252"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["508"], locs["252"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["30"], locs["861"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["228"], locs["1012"], regs[3]);
    info.eval->add(locs["781"], locs["893"], regs[4]);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    