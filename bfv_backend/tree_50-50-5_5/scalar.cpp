
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 9;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"199", "402", "317", "54", "546", "158", "827", "857", "421", "982"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["402"], locs["54"], regs[0]);
    info.eval->multiply(regs[0], locs["317"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[1], locs["982"], regs[2]);
    info.eval->add(locs["546"], regs[2], regs[3]);
    info.eval->add(locs["857"], locs["421"], regs[4]);
    info.eval->add(regs[4], locs["158"], regs[5]);
    info.eval->add(regs[5], locs["827"], regs[6]);
    info.eval->multiply(regs[6], locs["199"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(regs[3], regs[7], regs[8]);
    std::vector<ctxt> answer;
    answer.push_back(regs[8]);
    return answer;
}
    