
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 91;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"max_value_packed_fully(cs):2", "max_value_packed_fully(os):1", "max_value_packed_fully(os):0", "max_value_packed_fully(cs):8", "1", "max_value_packed_fully(cs):1", "max_value_packed_fully(cs):0", "max_value_packed_fully(cs):4", "max_value_packed_fully(cs):7", "max_value_packed_fully(cs):3", "max_value_packed_fully(os):3", "max_value_packed_fully(cs):5", "max_value_packed_fully(cs):9", "max_value_packed_fully(os):2", "max_value_packed_fully(cs):6", "max_value_packed_fully(os):4"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["max_value_packed_fully(cs):0"];
    regs[1] = locs["max_value_packed_fully(cs):1"];
    regs[2] = locs["max_value_packed_fully(cs):3"];
    regs[3] = locs["max_value_packed_fully(cs):6"];
    regs[4] = locs["max_value_packed_fully(os):0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(locs["1"], regs[3], regs[6]);
    regs[7] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->multiply(regs[2], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(locs["1"], regs[2], regs[11]);
    regs[12] = locs["max_value_packed_fully(cs):7"];
    regs[13] = locs["max_value_packed_fully(os):3"];
    info.eval->multiply(regs[12], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["1"], regs[12], regs[15]);
    regs[16] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[14], regs[17], regs[18]);
    info.eval->multiply(regs[11], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[10], regs[19], regs[20]);
    info.eval->multiply(regs[1], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(locs["1"], regs[1], regs[22]);
    regs[23] = locs["max_value_packed_fully(cs):4"];
    regs[24] = locs["max_value_packed_fully(cs):8"];
    regs[25] = locs["max_value_packed_fully(os):2"];
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(locs["1"], regs[24], regs[27]);
    regs[28] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[27], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[26], regs[29], regs[30]);
    info.eval->multiply(regs[23], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(locs["1"], regs[23], regs[32]);
    regs[33] = locs["max_value_packed_fully(cs):7"];
    regs[34] = locs["max_value_packed_fully(os):3"];
    info.eval->multiply(regs[33], regs[34], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(locs["1"], regs[33], regs[36]);
    regs[37] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[36], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[35], regs[38], regs[39]);
    info.eval->multiply(regs[32], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[31], regs[40], regs[41]);
    info.eval->multiply(regs[22], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->add(regs[21], regs[42], regs[43]);
    info.eval->multiply(regs[0], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(locs["1"], regs[0], regs[45]);
    regs[46] = locs["max_value_packed_fully(cs):2"];
    regs[47] = locs["max_value_packed_fully(cs):5"];
    regs[48] = locs["max_value_packed_fully(cs):9"];
    regs[49] = locs["max_value_packed_fully(os):1"];
    info.eval->multiply(regs[48], regs[49], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(locs["1"], regs[48], regs[51]);
    regs[52] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[51], regs[52], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[50], regs[53], regs[54]);
    info.eval->multiply(regs[47], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(locs["1"], regs[47], regs[56]);
    regs[57] = locs["max_value_packed_fully(cs):7"];
    regs[58] = locs["max_value_packed_fully(os):3"];
    info.eval->multiply(regs[57], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(locs["1"], regs[57], regs[60]);
    regs[61] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[60], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->add(regs[59], regs[62], regs[63]);
    info.eval->multiply(regs[56], regs[63], regs[64]);
    info.eval->relinearize_inplace(regs[64], rk);
    info.eval->add(regs[55], regs[64], regs[65]);
    info.eval->multiply(regs[46], regs[65], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    info.eval->add(locs["1"], regs[46], regs[67]);
    regs[68] = locs["max_value_packed_fully(cs):4"];
    regs[69] = locs["max_value_packed_fully(cs):8"];
    regs[70] = locs["max_value_packed_fully(os):2"];
    info.eval->multiply(regs[69], regs[70], regs[71]);
    info.eval->relinearize_inplace(regs[71], rk);
    info.eval->add(locs["1"], regs[69], regs[72]);
    regs[73] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[72], regs[73], regs[74]);
    info.eval->relinearize_inplace(regs[74], rk);
    info.eval->add(regs[71], regs[74], regs[75]);
    info.eval->multiply(regs[68], regs[75], regs[76]);
    info.eval->relinearize_inplace(regs[76], rk);
    info.eval->add(locs["1"], regs[68], regs[77]);
    regs[78] = locs["max_value_packed_fully(cs):7"];
    regs[79] = locs["max_value_packed_fully(os):3"];
    info.eval->multiply(regs[78], regs[79], regs[80]);
    info.eval->relinearize_inplace(regs[80], rk);
    info.eval->add(locs["1"], regs[78], regs[81]);
    regs[82] = locs["max_value_packed_fully(os):4"];
    info.eval->multiply(regs[81], regs[82], regs[83]);
    info.eval->relinearize_inplace(regs[83], rk);
    info.eval->add(regs[80], regs[83], regs[84]);
    info.eval->multiply(regs[77], regs[84], regs[85]);
    info.eval->relinearize_inplace(regs[85], rk);
    info.eval->add(regs[76], regs[85], regs[86]);
    info.eval->multiply(regs[67], regs[86], regs[87]);
    info.eval->relinearize_inplace(regs[87], rk);
    info.eval->add(regs[66], regs[87], regs[88]);
    info.eval->multiply(regs[45], regs[88], regs[89]);
    info.eval->relinearize_inplace(regs[89], rk);
    info.eval->add(regs[44], regs[89], regs[90]);
    std::vector<ctxt> answer;
    answer.push_back(regs[90]);
    return answer;
}
    