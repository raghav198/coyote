
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"880", "826", "722", "691", "447", "744", "756", "485"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["756"], locs["722"], regs[0]);
    info.eval->add(locs["880"], locs["447"], regs[1]);
    info.eval->multiply(locs["485"], locs["826"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[1], regs[2], regs[3]);
    info.eval->add(locs["691"], regs[3], regs[4]);
    info.eval->multiply(regs[4], locs["744"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[0], regs[5], regs[6]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    