
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:2", "b:0", "a:0", "d:0", "d:2", "c:1", "d:1", "b:1", "a:1", "c:0", "a:2", "c:2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->sub(locs["a:0"], locs["c:0"], regs[0]);
    info.eval->sub(locs["a:0"], locs["c:0"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->sub(locs["b:0"], locs["d:0"], regs[3]);
    info.eval->sub(locs["b:0"], locs["d:0"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->sub(locs["a:0"], locs["c:1"], regs[7]);
    info.eval->sub(locs["a:0"], locs["c:1"], regs[8]);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->sub(locs["b:0"], locs["d:1"], regs[10]);
    info.eval->sub(locs["b:0"], locs["d:1"], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->sub(locs["a:0"], locs["c:2"], regs[14]);
    info.eval->sub(locs["a:0"], locs["c:2"], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->sub(locs["b:0"], locs["d:2"], regs[17]);
    info.eval->sub(locs["b:0"], locs["d:2"], regs[18]);
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    info.eval->sub(locs["a:1"], locs["c:0"], regs[21]);
    info.eval->sub(locs["a:1"], locs["c:0"], regs[22]);
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->sub(locs["b:1"], locs["d:0"], regs[24]);
    info.eval->sub(locs["b:1"], locs["d:0"], regs[25]);
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[23], regs[26], regs[27]);
    info.eval->sub(locs["a:1"], locs["c:1"], regs[28]);
    info.eval->sub(locs["a:1"], locs["c:1"], regs[29]);
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->sub(locs["b:1"], locs["d:1"], regs[31]);
    info.eval->sub(locs["b:1"], locs["d:1"], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[30], regs[33], regs[34]);
    info.eval->sub(locs["a:1"], locs["c:2"], regs[35]);
    info.eval->sub(locs["a:1"], locs["c:2"], regs[36]);
    info.eval->multiply(regs[35], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->sub(locs["b:1"], locs["d:2"], regs[38]);
    info.eval->sub(locs["b:1"], locs["d:2"], regs[39]);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[37], regs[40], regs[41]);
    info.eval->sub(locs["a:2"], locs["c:0"], regs[42]);
    info.eval->sub(locs["a:2"], locs["c:0"], regs[43]);
    info.eval->multiply(regs[42], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->sub(locs["b:2"], locs["d:0"], regs[45]);
    info.eval->sub(locs["b:2"], locs["d:0"], regs[46]);
    info.eval->multiply(regs[45], regs[46], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[44], regs[47], regs[48]);
    info.eval->sub(locs["a:2"], locs["c:1"], regs[49]);
    info.eval->sub(locs["a:2"], locs["c:1"], regs[50]);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->sub(locs["b:2"], locs["d:1"], regs[52]);
    info.eval->sub(locs["b:2"], locs["d:1"], regs[53]);
    info.eval->multiply(regs[52], regs[53], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[51], regs[54], regs[55]);
    info.eval->sub(locs["a:2"], locs["c:2"], regs[56]);
    info.eval->sub(locs["a:2"], locs["c:2"], regs[57]);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->sub(locs["b:2"], locs["d:2"], regs[59]);
    info.eval->sub(locs["b:2"], locs["d:2"], regs[60]);
    info.eval->multiply(regs[59], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->add(regs[58], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[13]);
    answer.push_back(regs[20]);
    answer.push_back(regs[27]);
    answer.push_back(regs[34]);
    answer.push_back(regs[41]);
    answer.push_back(regs[48]);
    answer.push_back(regs[55]);
    answer.push_back(regs[62]);
    return answer;
}
    