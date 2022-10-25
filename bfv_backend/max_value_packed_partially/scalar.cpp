
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 80;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"1", "max_value_packed_partially(cs):4", "max_value_packed_partially(os):2", "max_value_packed_partially(cs):9", "max_value_packed_partially(os):3", "max_value_packed_partially(cs):2", "max_value_packed_partially(cs):5", "max_value_packed_partially(os):4", "max_value_packed_partially(cs):1", "max_value_packed_partially(cs):3", "max_value_packed_partially(cs):7", "max_value_packed_partially(os):0", "max_value_packed_partially(os):1", "max_value_packed_partially(cs):0", "max_value_packed_partially(cs):8", "max_value_packed_partially(cs):6"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["max_value_packed_partially(cs):0"];
    regs[1] = locs["max_value_packed_partially(cs):1"];
    regs[2] = locs["max_value_packed_partially(cs):3"];
    regs[3] = locs["max_value_packed_partially(cs):6"];
    regs[4] = locs["max_value_packed_partially(os):0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(locs["1"], regs[3], regs[6]);
    regs[7] = locs["max_value_packed_partially(os):4"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->multiply(regs[2], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(locs["1"], regs[2], regs[11]);
    regs[12] = locs["max_value_packed_partially(cs):7"];
    regs[13] = locs["max_value_packed_partially(os):3"];
    info.eval->multiply(regs[12], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["1"], regs[12], regs[15]);
    info.eval->multiply(regs[15], regs[7], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[14], regs[16], regs[17]);
    info.eval->multiply(regs[11], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[10], regs[18], regs[19]);
    info.eval->multiply(regs[1], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(locs["1"], regs[1], regs[21]);
    regs[22] = locs["max_value_packed_partially(cs):4"];
    regs[23] = locs["max_value_packed_partially(cs):8"];
    regs[24] = locs["max_value_packed_partially(os):2"];
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(locs["1"], regs[23], regs[26]);
    info.eval->multiply(regs[26], regs[7], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[25], regs[27], regs[28]);
    info.eval->multiply(regs[22], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(locs["1"], regs[22], regs[30]);
    regs[31] = locs["max_value_packed_partially(cs):7"];
    info.eval->multiply(regs[31], regs[13], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(locs["1"], regs[31], regs[33]);
    info.eval->multiply(regs[33], regs[7], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->add(regs[32], regs[34], regs[35]);
    info.eval->multiply(regs[30], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[29], regs[36], regs[37]);
    info.eval->multiply(regs[21], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[20], regs[38], regs[39]);
    info.eval->multiply(regs[0], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(locs["1"], regs[0], regs[41]);
    regs[42] = locs["max_value_packed_partially(cs):2"];
    regs[43] = locs["max_value_packed_partially(cs):5"];
    regs[44] = locs["max_value_packed_partially(cs):9"];
    regs[45] = locs["max_value_packed_partially(os):1"];
    info.eval->multiply(regs[44], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->add(locs["1"], regs[44], regs[47]);
    info.eval->multiply(regs[47], regs[7], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[46], regs[48], regs[49]);
    info.eval->multiply(regs[43], regs[49], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(locs["1"], regs[43], regs[51]);
    regs[52] = locs["max_value_packed_partially(cs):7"];
    info.eval->multiply(regs[52], regs[13], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(locs["1"], regs[52], regs[54]);
    info.eval->multiply(regs[54], regs[7], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[53], regs[55], regs[56]);
    info.eval->multiply(regs[51], regs[56], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->add(regs[50], regs[57], regs[58]);
    info.eval->multiply(regs[42], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(locs["1"], regs[42], regs[60]);
    regs[61] = locs["max_value_packed_partially(cs):4"];
    regs[62] = locs["max_value_packed_partially(cs):8"];
    info.eval->multiply(regs[62], regs[24], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->add(locs["1"], regs[62], regs[64]);
    info.eval->multiply(regs[64], regs[7], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    info.eval->add(regs[63], regs[65], regs[66]);
    info.eval->multiply(regs[61], regs[66], regs[67]);
    info.eval->relinearize_inplace(regs[67], rk);
    info.eval->add(locs["1"], regs[61], regs[68]);
    regs[69] = locs["max_value_packed_partially(cs):7"];
    info.eval->multiply(regs[69], regs[13], regs[70]);
    info.eval->relinearize_inplace(regs[70], rk);
    info.eval->add(locs["1"], regs[69], regs[71]);
    info.eval->multiply(regs[71], regs[7], regs[72]);
    info.eval->relinearize_inplace(regs[72], rk);
    info.eval->add(regs[70], regs[72], regs[73]);
    info.eval->multiply(regs[68], regs[73], regs[74]);
    info.eval->relinearize_inplace(regs[74], rk);
    info.eval->add(regs[67], regs[74], regs[75]);
    info.eval->multiply(regs[60], regs[75], regs[76]);
    info.eval->relinearize_inplace(regs[76], rk);
    info.eval->add(regs[59], regs[76], regs[77]);
    info.eval->multiply(regs[41], regs[77], regs[78]);
    info.eval->relinearize_inplace(regs[78], rk);
    info.eval->add(regs[40], regs[78], regs[79]);
    std::vector<ctxt> answer;
    answer.push_back(regs[79]);
    return answer;
}
    