// // Simplified, general-purpose ZK proof generator with unlinkable state transitions
// // Dependencies: libsnark or equivalent library
// #include <map>
// #include <vector>
// #include <string>
// #include <random>
// #include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
// #include <libsnark/relations/constraint_satisfaction_problems/r1cs/r1cs.hpp>
// #include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/examples/run_r1cs_ppzksnark.hpp>
// #include <libsnark/gadgetlib1/gadgets/hashes/sha256/sha256_gadget.hpp>
// #include <libsnark/gadgetlib1/gadget.hpp>
// #include <libsnark/gadgetlib1/gadgets/curves/edwards_gadgets.hpp>

// using namespace libsnark;
// using namespace std;
// using FieldT = libff::Fr<default_r1cs_ppzksnark_pp>;
// using EC_Group = libff::G1<default_r1cs_ppzksnark_pp>;

// //---------------------------------------------------
// // Data structures
// //---------------------------------------------------
// struct CommittedValue {
//     FieldT value;           // only used by prover
//     FieldT randomness;      // re-randomization parameter
//     libsnark::pedersen_commitment commitment; // commitment (hiding value)
// };

// struct ProofState {
//     vector<CommittedValue> hardClauses;
//     vector<CommittedValue> softClauses;
//     vector<CommittedValue> cardClauses;
//     CommittedValue LB;
//     CommittedValue UB;
// };

// struct Rule {
//     int id;
//     int type;                    // Rule type (1 to 5)
//     vector<int> clauses;        // IDs of clauses used/affected
// };

// struct RuleApplication {
//     int rule_type;
//     protoboard<FieldT> pb;
//     ProofState input;
//     ProofState output;
// };

// //---------------------------------------------------
// // Helper: Generate an elliptic curve Pedersen-style commitment
// //---------------------------------------------------
// EC_Group pedersen_commit(const FieldT &val, const FieldT &rand) {
//     static EC_Group G = EC_Group::one();                      // Base point for value
//     static EC_Group H = EC_Group::one().mul_by_cofactor();   // Independent base point for randomness
//     return G * val + H * rand;                                // EC Pedersen commitment
// }

// //---------------------------------------------------
// // Helper: Re-randomize a committed value
// //---------------------------------------------------
// CommittedValue rerandomize(const CommittedValue &cv) {
//     FieldT new_r = FieldT::random_element();
//     return {
//         cv.value,                      // same value
//         new_r,
//         pedersen_commit(cv.value, new_r) // new commitment
//     };
// }

// //---------------------------------------------------
// // Helper: Re-randomize entire proof state
// //---------------------------------------------------
// ProofState reblindState(const ProofState &ps) {
//     ProofState blinded;
//     for (auto &c : ps.hardClauses)  blinded.hardClauses.push_back(rerandomize(c));
//     for (auto &c : ps.softClauses)  blinded.softClauses.push_back(rerandomize(c));
//     for (auto &c : ps.cardClauses)  blinded.cardClauses.push_back(rerandomize(c));
//     blinded.LB = rerandomize(ps.LB);
//     blinded.UB = rerandomize(ps.UB);
//     return blinded;
// }

// //---------------------------------------------------
// // Commitment check gadget (in-circuit EC verification)
// //---------------------------------------------------
// void check_commitment(protoboard<FieldT> &pb,
//     pb_variable<FieldT> &val,
//     pb_variable<FieldT> &rand,
//     const EC_Group &expected_commitment) {
//     // EC base points
//     const EC_Group G = EC_Group::one();
//     const EC_Group H = EC_Group::one().mul_by_cofactor();

//     // Convert to variables
//     G1_variable<default_r1cs_ppzksnark_pp> G_var(pb, G);
//     G1_variable<default_r1cs_ppzksnark_pp> H_var(pb, H);
//     G1_variable<default_r1cs_ppzksnark_pp> expected_var(pb, expected_commitment);

//     // Allocate result of val*G
//     G1_variable<default_r1cs_ppzksnark_pp> valG(pb, "valG");
//     edwards_g1_scalarmul_gadget<default_r1cs_ppzksnark_pp> valG_mul(pb, G_var, val, valG);
//     valG_mul.generate_r1cs_constraints();
//     valG_mul.generate_r1cs_witness();

//     // Allocate result of rand*H
//     G1_variable<default_r1cs_ppzksnark_pp> randH(pb, "randH");
//     edwards_g1_scalarmul_gadget<default_r1cs_ppzksnark_pp> randH_mul(pb, H_var, rand, randH);
//     randH_mul.generate_r1cs_constraints();
//     randH_mul.generate_r1cs_witness();

//     // Add valG + randH = expected_commitment
//     G1_variable<default_r1cs_ppzksnark_pp> result(pb, "result");
//     edwards_g1_add_gadget<default_r1cs_ppzksnark_pp> add(pb, valG, randH, result);
//     add.generate_r1cs_constraints();
//     add.generate_r1cs_witness();

//     // Enforce equality: result == expected_commitment
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, result.X - expected_var.X, 0), "X check");
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, result.Y - expected_var.Y, 0), "Y check");
// }

// //---------------------------------------------------
// // Main: Generate unlinkable ZK proof folder
// //---------------------------------------------------
// vector<RuleApplication> buildZKProofFolder(
//     const map<int, ProofState> &proofStatesLog,
//     const map<int, Rule> &ruleLog
// ) {
//     vector<RuleApplication> folder;

//     for (const auto &[id, rule] : ruleLog) {
//         // Original states
//         const ProofState &original_in = proofStatesLog.at(id);
//         const ProofState &original_out = proofStatesLog.at(id + 1);

//         // Re-randomized states
//         ProofState blinded_in  = reblindState(original_in);
//         ProofState blinded_out = reblindState(original_out);

//         // Rule-specific ZK proof generation (abstracted)
//         protoboard<FieldT> pb;
//         if (rule.type == 1)
//             pb = rule1(blinded_in, blinded_out, rule.clauses);
//         else if (rule.type == 2)
//             pb = rule2(blinded_in, blinded_out, rule.clauses);
//         else if (rule.type == 3)
//             pb = rule3(blinded_in, blinded_out, rule.clauses);
//         else if (rule.type == 4)
//             pb = rule4(blinded_in, blinded_out, rule.clauses);
//         else if (rule.type == 5)
//             pb = rule5(blinded_in, blinded_out, rule.clauses);

//         folder.push_back({rule.type, pb, blinded_in, blinded_out});
//     }

//     return folder;
// }

// void build_rule1_circuit(protoboard<FieldT>& pb, 
//     const CommittedValue& LB_in,
//     const CommittedValue& weight,
//     const CommittedValue& LB_out)
// {
//     // === Declare variables ===
//     pb_variable<FieldT> lb;     // original LB value
//     pb_variable<FieldT> w;      // clause weight
//     pb_variable<FieldT> lb_new; // new LB
//     pb_variable<FieldT> r_in, r_out;

//     // === Allocate variables ===
//     lb.allocate(pb, "LB");
//     w.allocate(pb, "w");
//     lb_new.allocate(pb, "LB'");
//     r_in.allocate(pb, "r_in");
//     r_out.allocate(pb, "r_out");

//     // === Add constraints ===
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, lb + w, lb_new), "LB' = LB + w");

//     // === Commitment checks ===
//     commitment_t C_LB_in = LB_in.commitment;
//     commitment_t C_LB_out = LB_out.commitment;

//     // Check LB_in commitment
//     check_commitment(pb, lb, r_in, C_LB_in);     // Enforce: C_LB_in = lb * G + r_in * H

//     // Check LB_out commitment
//     check_commitment(pb, lb_new, r_out, C_LB_out); // Enforce: C_LB_out = lb_new * G + r_out * H

//     // === Set witness ===
//     pb.val(lb) = LB_in.value;
//     pb.val(w) = weight.value;
//     pb.val(lb_new) = LB_in.value + weight.value;
//     pb.val(r_in) = LB_in.randomness;
//     pb.val(r_out) = LB_out.randomness;
// }
