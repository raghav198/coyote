
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 46;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"941", "661", "879", "100", "1018", "577", "972", "382", "797", "427", "672", "359", "637", "14", "375", "993", "827", "801", "956", "197", "579", "696", "345", "94", "72", "611", "151", "252", "387", "948", "15", "689", "397", "367", "263", "275", "713", "841", "168", "901", "650", "921", "365", "354", "636", "606", "385"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["941"], locs["993"], regs[0]);
    info.eval->add(locs["879"], regs[0], regs[1]);
    info.eval->multiply(locs["577"], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["382"], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[3], locs["637"], regs[4]);
    info.eval->add(locs["15"], locs["611"], regs[5]);
    info.eval->add(locs["385"], locs["1018"], regs[6]);
    info.eval->multiply(regs[5], regs[6], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["672"], locs["841"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[8], locs["367"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(regs[7], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(regs[10], locs["263"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(locs["801"], locs["197"], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(regs[12], locs["151"], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(locs["365"], locs["827"], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(regs[14], locs["397"], regs[15]);
    info.eval->multiply(locs["168"], locs["650"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(locs["427"], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(regs[15], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[13], regs[18], regs[19]);
    info.eval->multiply(regs[11], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[4], regs[20], regs[21]);
    info.eval->multiply(regs[21], locs["636"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs["359"], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(locs["375"], locs["689"], regs[24]);
    info.eval->add(regs[24], locs["275"], regs[25]);
    info.eval->multiply(locs["72"], locs["921"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[26], locs["354"], regs[27]);
    info.eval->multiply(regs[25], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[28], locs["661"], regs[29]);
    info.eval->multiply(locs["100"], locs["252"], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(regs[30], locs["579"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(regs[31], locs["972"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(locs["948"], locs["606"], regs[33]);
    info.eval->add(locs["713"], regs[33], regs[34]);
    info.eval->add(locs["94"], locs["797"], regs[35]);
    info.eval->add(regs[35], locs["901"], regs[36]);
    info.eval->multiply(regs[34], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(regs[32], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[29], regs[38], regs[39]);
    info.eval->add(regs[39], locs["387"], regs[40]);
    info.eval->add(locs["696"], regs[40], regs[41]);
    info.eval->add(regs[41], locs["345"], regs[42]);
    info.eval->multiply(regs[23], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(locs["14"], locs["956"], regs[44]);
    info.eval->multiply(regs[43], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[45]);
    return answer;
}
    