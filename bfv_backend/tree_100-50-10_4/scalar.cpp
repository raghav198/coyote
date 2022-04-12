
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 21;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"638", "651", "430", "369", "133", "78", "14", "104", "598", "185", "325", "1013", "883", "477", "108", "782", "272", "262", "945", "184", "639", "206"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["325"], locs["369"], regs[0]);
    info.eval->add(locs["430"], locs["133"], regs[1]);
    info.eval->multiply(locs["638"], locs["651"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["78"], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[3], locs["477"], regs[4]);
    info.eval->multiply(regs[4], locs["272"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[1], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["639"], locs["598"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(locs["108"], regs[7], regs[8]);
    info.eval->multiply(regs[6], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["206"], locs["262"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[10], locs["104"], regs[11]);
    info.eval->multiply(regs[9], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[12], locs["184"], regs[13]);
    info.eval->add(locs["14"], locs["883"], regs[14]);
    info.eval->multiply(locs["185"], locs["945"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(regs[15], locs["1013"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[14], regs[16], regs[17]);
    info.eval->multiply(regs[17], locs["782"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(regs[13], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[0], regs[19], regs[20]);
    std::vector<ctxt> answer;
    answer.push_back(regs[20]);
    return answer;
}
    