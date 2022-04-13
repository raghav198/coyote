
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 21;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"706", "469", "723", "427", "775", "2", "709", "669", "988", "759", "912", "729", "461", "208", "359", "660", "113", "538", "786", "877", "420", "1000"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["420"], locs["359"], regs[0]);
    info.eval->add(locs["877"], locs["461"], regs[1]);
    info.eval->add(locs["709"], regs[1], regs[2]);
    info.eval->multiply(regs[2], locs["912"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["1000"], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[0], regs[4], regs[5]);
    info.eval->add(locs["208"], regs[5], regs[6]);
    info.eval->add(locs["759"], locs["775"], regs[7]);
    info.eval->add(locs["729"], regs[7], regs[8]);
    info.eval->multiply(locs["660"], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(locs["723"], regs[9], regs[10]);
    info.eval->add(locs["786"], locs["2"], regs[11]);
    info.eval->add(regs[11], locs["669"], regs[12]);
    info.eval->add(locs["706"], regs[12], regs[13]);
    info.eval->add(regs[13], locs["469"], regs[14]);
    info.eval->add(regs[10], regs[14], regs[15]);
    info.eval->multiply(regs[15], locs["988"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[16], locs["427"], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["113"], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(regs[18], locs["538"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[6], regs[19], regs[20]);
    std::vector<ctxt> answer;
    answer.push_back(regs[20]);
    return answer;
}
    