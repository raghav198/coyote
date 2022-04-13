
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 30;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"664", "920", "787", "965", "565", "498", "636", "493", "935", "224", "337", "712", "38", "625", "117", "829", "16", "617", "976", "132", "264", "972", "551", "274", "567", "758", "40", "748", "450", "365"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["920"], locs["40"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(regs[0], locs["935"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[1], locs["224"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["498"], locs["493"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[3], locs["748"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["617"], locs["551"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["758"], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(regs[4], regs[6], regs[7]);
    info.eval->add(regs[7], locs["972"], regs[8]);
    info.eval->add(locs["712"], regs[8], regs[9]);
    info.eval->multiply(locs["337"], locs["132"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(regs[10], locs["976"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(locs["567"], locs["38"], regs[12]);
    info.eval->multiply(locs["565"], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[11], regs[13], regs[14]);
    info.eval->multiply(regs[14], locs["664"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(regs[15], locs["264"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[9], regs[16], regs[17]);
    info.eval->add(regs[17], locs["965"], regs[18]);
    info.eval->add(locs["787"], locs["625"], regs[19]);
    info.eval->add(locs["829"], locs["117"], regs[20]);
    info.eval->multiply(locs["450"], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(regs[19], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(regs[22], locs["274"], regs[23]);
    info.eval->multiply(locs["636"], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(locs["365"], locs["16"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(regs[18], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[27], locs["132"], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(regs[2], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[29]);
    return answer;
}
    