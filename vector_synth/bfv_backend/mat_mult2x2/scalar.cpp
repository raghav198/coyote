
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 20;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:0,0", "a:0,1", "a:1,1", "a:1,0", "b:1,0", "b:1,1", "a:0,0", "b:0,1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0,0"];
    regs[1] = locs["b:0,0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["a:0,1"];
    regs[4] = locs["b:1,0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["b:0,1"];
    info.eval->multiply(regs[0], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["b:1,1"];
    info.eval->multiply(regs[3], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[8], regs[10], regs[11]);
    regs[12] = locs["a:1,0"];
    info.eval->multiply(regs[12], regs[1], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["a:1,1"];
    info.eval->multiply(regs[14], regs[4], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[13], regs[15], regs[16]);
    info.eval->multiply(regs[12], regs[7], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(regs[14], regs[9], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[17], regs[18], regs[19]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[11]);
    answer.push_back(regs[16]);
    answer.push_back(regs[19]);
    return answer;
}
    