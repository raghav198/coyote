
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 3;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"338", "295", "542", "1022"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["1022"], locs["295"], regs[0]);
    info.eval->multiply(locs["338"], regs[0], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[1], locs["542"], regs[2]);
    std::vector<ctxt> answer;
    answer.push_back(regs[2]);
    return answer;
}
    