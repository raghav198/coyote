
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 11;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:2", "b:1", "a:3", "b:4", "b:3", "a:1", "b:5", "a:4", "a:2", "a:0", "b:0", "a:5"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["a:0"], locs["b:0"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["a:1"], locs["b:1"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(locs["a:2"], locs["b:2"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[1], regs[2], regs[3]);
    info.eval->add(regs[0], regs[3], regs[4]);
    info.eval->multiply(locs["a:3"], locs["b:3"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["a:4"], locs["b:4"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["a:5"], locs["b:5"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(regs[6], regs[7], regs[8]);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[4], regs[9], regs[10]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    return answer;
}
    