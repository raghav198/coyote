
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 14;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"2", "229", "46", "919", "858", "460", "965", "236", "585", "38", "956", "988", "666", "678"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["666"], locs["2"], regs[0]);
    info.eval->multiply(locs["460"], locs["46"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[1], locs["2"], regs[2]);
    info.eval->add(locs["956"], regs[2], regs[3]);
    info.eval->add(regs[3], locs["38"], regs[4]);
    info.eval->multiply(locs["965"], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[5], locs["236"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(regs[0], regs[6], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["678"], locs["858"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(locs["919"], locs["229"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["988"], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[10], locs["585"], regs[11]);
    info.eval->multiply(regs[8], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(regs[7], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[13]);
    return answer;
}
    