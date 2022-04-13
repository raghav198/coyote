
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 9;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"644", "170", "907", "17", "475", "966", "597", "563", "739", "24"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["24"], locs["644"], regs[0]);
    info.eval->add(regs[0], locs["17"], regs[1]);
    info.eval->add(locs["563"], regs[1], regs[2]);
    info.eval->multiply(locs["907"], locs["966"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(locs["739"], locs["170"], regs[5]);
    info.eval->add(locs["597"], regs[5], regs[6]);
    info.eval->add(locs["475"], regs[6], regs[7]);
    info.eval->multiply(regs[4], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[8]);
    return answer;
}
    