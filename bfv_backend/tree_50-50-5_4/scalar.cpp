
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 16;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"81", "842", "342", "619", "51", "29", "855", "959", "185", "900", "894", "405", "55", "683", "866", "633", "194"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["633"], locs["185"], regs[0]);
    info.eval->multiply(locs["619"], regs[0], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(locs["842"], locs["900"], regs[2]);
    info.eval->multiply(regs[2], locs["194"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["894"], locs["342"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[1], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["51"], locs["55"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["855"], locs["29"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[9], locs["405"], regs[10]);
    info.eval->add(locs["866"], locs["81"], regs[11]);
    info.eval->add(regs[11], locs["683"], regs[12]);
    info.eval->multiply(locs["959"], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[10], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(regs[6], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[15]);
    return answer;
}
    