
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"312", "1015", "232", "979", "947", "966", "685", "85", "987", "845", "799", "968", "204", "130", "5", "550", "245", "315", "258", "50", "928", "918", "754", "446", "973", "620", "560", "43", "780", "879", "874", "359", "1020", "757", "797", "878", "681", "760", "465", "8", "664", "340", "400", "922", "155", "407", "628", "766", "528", "624", "104", "935", "687", "875", "485", "497", "376", "1001", "849", "310", "30"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["497"], locs["797"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["928"], locs["312"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["400"], locs["340"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["973"], locs["628"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["620"], locs["85"], regs[7]);
    info.eval->add(locs["359"], locs["30"], regs[8]);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["315"], locs["766"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(locs["968"], locs["879"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["528"], locs["780"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["922"], locs["550"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(locs["799"], locs["446"], regs[18]);
    info.eval->multiply(locs["754"], locs["628"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[17], regs[20], regs[21]);
    info.eval->add(locs["465"], locs["258"], regs[22]);
    info.eval->add(locs["685"], locs["979"], regs[23]);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(locs["947"], locs["204"], regs[25]);
    info.eval->add(locs["628"], locs["310"], regs[26]);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->add(regs[21], regs[28], regs[29]);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(locs["50"], locs["155"], regs[31]);
    info.eval->add(locs["760"], locs["624"], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(locs["757"], locs["935"], regs[34]);
    info.eval->add(locs["687"], locs["987"], regs[35]);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["766"], locs["874"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["918"], locs["845"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["8"], locs["245"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(locs["849"], locs["681"], regs[42]);
    info.eval->add(regs[41], regs[42], regs[43]);
    info.eval->add(regs[40], regs[43], regs[44]);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->multiply(locs["1015"], locs["966"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->add(locs["407"], locs["875"], regs[47]);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(locs["560"], locs["130"], regs[49]);
    info.eval->add(locs["232"], locs["485"], regs[50]);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->multiply(locs["664"], locs["878"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(locs["1020"], locs["104"], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(locs["5"], locs["43"], regs[56]);
    info.eval->multiply(locs["376"], locs["1001"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[55], regs[58], regs[59]);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    