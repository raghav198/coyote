
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 9;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"758", "240", "384", "89", "588", "164", "151", "638", "24", "911"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["240"], locs["384"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["151"], locs["911"], regs[1]);
    info.eval->multiply(regs[1], locs["638"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["758"], locs["588"], regs[3]);
    info.eval->multiply(regs[3], locs["89"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[2], regs[4], regs[5]);
    info.eval->add(regs[0], regs[5], regs[6]);
    info.eval->multiply(regs[6], locs["24"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["164"], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[8]);
    return answer;
}
    