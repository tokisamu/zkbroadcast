#include "../src/sigmaplus_prover.h"
#include "../src/sigmaplus_verifier.h"
namespace sigma {
template <class Exponent, class GroupElement>
class Message{

public:
    Message(int id,char *mes, int time,SigmaPlusProof<Exponent, GroupElement>* proof_out);
    int message_id;
    char *message;
    int timestamp;
    sigma::SigmaPlusProof<Exponent,GroupElement> *proof;
};
}
