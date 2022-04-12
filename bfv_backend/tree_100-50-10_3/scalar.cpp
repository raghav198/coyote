
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 16;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"514", "825", "474", "581", "173", "459", "928", "575", "468", "276", "833", "266", "228", "624", "922", "618", "664"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["173"], locs["922"], regs[0]);
    info.eval->multiply(locs["581"], locs["624"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["459"], regs[2], regs[3]);
    info.eval->multiply(locs["575"], locs["266"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["928"], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[5], locs["825"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(regs[6], locs["276"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["468"], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(locs["833"], locs["474"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(regs[9], locs["228"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(regs[10], locs["618"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[8], regs[11], regs[12]);
    info.eval->add(locs["514"], regs[12], regs[13]);
    info.eval->add(locs["664"], regs[13], regs[14]);
    info.eval->add(regs[3], regs[14], regs[15]);
    std::vector<ctxt> answer;
    answer.push_back(regs[15]);
    return answer;
}
    