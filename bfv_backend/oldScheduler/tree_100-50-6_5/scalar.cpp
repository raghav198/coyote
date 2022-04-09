
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"825", "385", "45", "282", "971", "1019", "788", "1012", "344", "150", "781", "69", "222", "927", "854", "922", "981", "817", "873", "95", "228", "821", "153", "591", "194", "1015", "890", "940", "252", "205", "35", "640", "389", "409", "935", "114", "137", "400", "742", "470", "694", "178", "576", "793", "198", "309", "976", "290", "794", "985", "893", "56", "471", "762", "665", "909", "847", "130", "936", "751", "752", "498"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["228"], locs["1012"], regs[0]);
    info.eval->add(locs["781"], locs["893"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["194"], locs["981"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["971"], locs["389"], regs[4]);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->add(locs["781"], locs["409"], regs[7]);
    info.eval->add(locs["640"], locs["927"], regs[8]);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(locs["694"], locs["752"], regs[10]);
    info.eval->multiply(locs["873"], locs["205"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["751"], locs["821"], regs[15]);
    info.eval->add(locs["45"], locs["935"], regs[16]);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["794"], locs["976"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["576"], locs["56"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[17], regs[20], regs[21]);
    info.eval->add(locs["940"], locs["470"], regs[22]);
    info.eval->multiply(locs["252"], locs["498"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->add(locs["69"], locs["309"], regs[25]);
    info.eval->add(locs["1019"], locs["153"], regs[26]);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[14], regs[29], regs[30]);
    info.eval->add(locs["95"], locs["936"], regs[31]);
    info.eval->multiply(locs["817"], locs["591"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(locs["825"], locs["137"], regs[34]);
    info.eval->multiply(locs["985"], locs["400"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->add(locs["471"], locs["282"], regs[38]);
    info.eval->multiply(locs["178"], locs["130"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["222"], locs["793"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(locs["385"], locs["909"], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[40], regs[43], regs[44]);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->multiply(locs["290"], locs["114"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["198"], locs["35"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(locs["1015"], locs["854"], regs[49]);
    info.eval->multiply(locs["890"], locs["470"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->multiply(locs["788"], locs["742"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->multiply(locs["762"], locs["344"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->add(locs["665"], locs["150"], regs[56]);
    info.eval->add(locs["922"], locs["847"], regs[57]);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->add(regs[55], regs[58], regs[59]);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->add(regs[45], regs[60], regs[61]);
    info.eval->add(regs[30], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    