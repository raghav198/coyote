
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"963", "903", "536", "860", "239", "96", "895", "733"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["860"], locs["536"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["895"], locs["963"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["96"], locs["903"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["239"], locs["733"], regs[4]);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    