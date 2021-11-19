
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 11;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"293", "788", "408", "345", "953", "44", "59", "1013", "92", "179", "208", "974"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["788"], locs["408"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["44"], locs["345"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["92"], regs[2], regs[3]);
    info.eval->multiply(locs["293"], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["179"], locs["1013"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[5], locs["953"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["974"], regs[6], regs[7]);
    info.eval->multiply(regs[7], locs["208"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[4], regs[8], regs[9]);
    info.eval->multiply(locs["59"], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    return answer;
}
    