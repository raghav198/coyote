
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 13;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"241", "872", "159", "898", "170", "70", "225", "129", "801", "317", "840", "805", "319", "436"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["70"], locs["159"], regs[0]);
    info.eval->multiply(locs["317"], locs["241"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[1], locs["319"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["898"], locs["801"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[3], locs["436"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[2], regs[4], regs[5]);
    info.eval->add(locs["840"], locs["805"], regs[6]);
    info.eval->add(regs[6], locs["170"], regs[7]);
    info.eval->add(locs["225"], locs["872"], regs[8]);
    info.eval->add(regs[8], locs["129"], regs[9]);
    info.eval->multiply(regs[7], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(regs[5], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[0], regs[11], regs[12]);
    std::vector<ctxt> answer;
    answer.push_back(regs[12]);
    return answer;
}
    