
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 13;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"233", "80", "1008", "1019", "149", "35", "737", "231", "493", "469", "638", "506", "645", "805"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["645"], locs["638"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["35"], regs[0], regs[1]);
    info.eval->multiply(regs[1], locs["805"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["506"], locs["737"], regs[3]);
    info.eval->multiply(locs["231"], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[2], regs[4], regs[5]);
    info.eval->multiply(locs["493"], locs["469"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["1008"], locs["233"], regs[7]);
    info.eval->add(regs[6], regs[7], regs[8]);
    info.eval->add(regs[8], locs["1019"], regs[9]);
    info.eval->add(locs["149"], regs[9], regs[10]);
    info.eval->add(regs[5], regs[10], regs[11]);
    info.eval->add(regs[11], locs["80"], regs[12]);
    std::vector<ctxt> answer;
    answer.push_back(regs[12]);
    return answer;
}
    