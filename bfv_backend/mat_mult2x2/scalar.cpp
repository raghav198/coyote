
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 12;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:0,0", "a:1,0", "b:1,0", "b:1,1", "b:0,1", "a:1,1", "a:0,0", "a:0,1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["a:0,0"], locs["b:0,0"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["a:0,1"], locs["b:1,0"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["a:0,0"], locs["b:0,1"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["a:0,1"], locs["b:1,1"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(locs["a:1,0"], locs["b:0,0"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["a:1,1"], locs["b:1,0"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(regs[6], regs[7], regs[8]);
    info.eval->multiply(locs["a:1,0"], locs["b:0,1"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["a:1,1"], locs["b:1,1"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[9], regs[10], regs[11]);
    std::vector<ctxt> answer;
    answer.push_back(regs[2]);
    answer.push_back(regs[5]);
    answer.push_back(regs[8]);
    answer.push_back(regs[11]);
    return answer;
}
    