namespace sigma {
    template<class Exponent, class GroupElement>
    Message<Exponent, GroupElement>::Message(int id,char* mes, int time,SigmaPlusProof<Exponent, GroupElement>* proof_out)
    {
        message_id = id;
        message = mes;
        timestamp = time;
        proof = proof_out;
    };
}