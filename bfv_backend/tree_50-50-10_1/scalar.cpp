
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 32;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"645", "574", "827", "500", "441", "456", "727", "478", "534", "387", "870", "918", "178", "327", "115", "27", "592", "402", "675", "591", "990", "221", "407", "1022", "422", "348", "271", "823", "184", "890", "589", "914"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["870"], locs["645"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["918"], locs["407"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["327"], regs[2], regs[3]);
    info.eval->add(locs["827"], locs["591"], regs[4]);
    info.eval->add(regs[4], locs["914"], regs[5]);
    info.eval->multiply(locs["221"], locs["727"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(regs[6], locs["990"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(regs[5], regs[7], regs[8]);
    info.eval->add(regs[3], regs[8], regs[9]);
    info.eval->multiply(locs["27"], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["271"], locs["348"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[11], locs["115"], regs[12]);
    info.eval->multiply(regs[10], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[13], locs["27"], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["675"], locs["1022"], regs[15]);
    info.eval->multiply(regs[15], locs["441"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(locs["478"], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(regs[14], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(regs[18], locs["823"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(locs["178"], locs["589"], regs[20]);
    info.eval->add(locs["890"], regs[20], regs[21]);
    info.eval->multiply(locs["456"], locs["500"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs["534"], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(locs["592"], locs["402"], regs[24]);
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(regs[25], locs["387"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(locs["184"], regs[26], regs[27]);
    info.eval->add(regs[21], regs[27], regs[28]);
    info.eval->multiply(locs["574"], locs["422"], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(regs[19], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[31]);
    return answer;
}
    