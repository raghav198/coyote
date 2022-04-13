
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 28;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"456", "698", "947", "113", "372", "805", "619", "888", "548", "899", "467", "247", "1018", "301", "739", "909", "762", "190", "534", "722", "142", "843", "485", "893", "314", "854", "576", "481"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["909"], locs["301"], regs[0]);
    info.eval->multiply(locs["314"], locs["467"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(locs["854"], regs[1], regs[2]);
    info.eval->multiply(regs[2], locs["843"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["142"], locs["485"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["372"], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(locs["481"], regs[5], regs[6]);
    info.eval->add(regs[6], locs["947"], regs[7]);
    info.eval->add(regs[7], locs["888"], regs[8]);
    info.eval->multiply(locs["893"], locs["190"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["739"], locs["456"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(locs["534"], locs["899"], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(locs["698"], locs["576"], regs[13]);
    info.eval->add(locs["247"], regs[13], regs[14]);
    info.eval->multiply(regs[12], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(locs["1018"], locs["548"], regs[16]);
    info.eval->add(locs["113"], regs[16], regs[17]);
    info.eval->multiply(locs["722"], locs["805"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[18], locs["762"], regs[19]);
    info.eval->add(regs[17], regs[19], regs[20]);
    info.eval->add(regs[15], regs[20], regs[21]);
    info.eval->multiply(regs[9], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(regs[8], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->multiply(regs[3], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(regs[24], locs["619"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(locs["142"], regs[25], regs[26]);
    info.eval->add(regs[0], regs[26], regs[27]);
    std::vector<ctxt> answer;
    answer.push_back(regs[27]);
    return answer;
}
    