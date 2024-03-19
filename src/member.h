#include "../src/sigmaplus_prover.h"
#include "../src/sigmaplus_verifier.h"
namespace sigma {
class Member{

public:
    Member();
    int user_id;
    secp_primitives::GroupElement commit;
    secp_primitives::Scalar secret;
};
}
