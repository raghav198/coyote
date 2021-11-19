
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"459", "549", "414", "530", "571", "399", "283", "881", "771", "68", "301", "747", "654", "945", "50", "193", "602", "985", "762", "155", "411", "994", "439", "737", "581", "646", "44", "314", "440", "161", "79", "248", "104", "604", "90", "47", "508", "810", "832", "974", "850", "972", "200", "885", "954", "489", "477", "909", "159", "222", "526", "305", "655", "370", "610", "264", "877", "711", "152"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["459"], locs["655"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["439"], locs["79"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["283"], locs["646"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["508"], locs["604"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["161"], locs["47"], regs[7]);
    info.eval->multiply(locs["370"], locs["909"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(locs["602"], locs["489"], regs[10]);
    info.eval->add(locs["411"], locs["877"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->add(regs[6], regs[13], regs[14]);
    info.eval->add(locs["610"], locs["954"], regs[15]);
    info.eval->multiply(locs["974"], locs["530"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[15], regs[16], regs[17]);
    info.eval->multiply(locs["737"], locs["414"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["200"], locs["370"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["50"], locs["881"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["571"], locs["68"], regs[23]);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->add(locs["850"], locs["152"], regs[25]);
    info.eval->multiply(locs["159"], locs["654"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[14], regs[29], regs[30]);
    info.eval->add(locs["549"], locs["945"], regs[31]);
    info.eval->add(locs["747"], locs["711"], regs[32]);
    info.eval->add(regs[31], regs[32], regs[33]);
    info.eval->multiply(locs["985"], locs["526"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->add(locs["159"], locs["477"], regs[35]);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[33], regs[36], regs[37]);
    info.eval->multiply(locs["104"], locs["762"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(locs["305"], locs["155"], regs[39]);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->add(locs["90"], locs["571"], regs[41]);
    info.eval->add(locs["810"], locs["314"], regs[42]);
    info.eval->add(regs[41], regs[42], regs[43]);
    info.eval->add(regs[40], regs[43], regs[44]);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->add(locs["972"], locs["399"], regs[46]);
    info.eval->add(locs["994"], locs["885"], regs[47]);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->multiply(locs["193"], locs["771"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(locs["581"], locs["222"], regs[50]);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->multiply(regs[48], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(locs["248"], locs["508"], regs[53]);
    info.eval->multiply(locs["314"], locs["440"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->add(locs["301"], locs["44"], regs[56]);
    info.eval->multiply(locs["832"], locs["264"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    