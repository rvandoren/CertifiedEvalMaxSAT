#include "proof_logger.h"
#include <fstream>
#include <sstream>
// #include <libsnark/gadgetlib1/protoboard.hpp>
// #include <libsnark/gadgetlib1/gadgets/hashes/sha256/sha256_gadget.hpp>
// #include <libff/common/utils.hpp>
#include <vector>
#include <string>
#include <iostream>
// #include <openssl/sha.h>
// #include <iomanip>
// #include <cstdint>

// using namespace libsnark;

int nodeCounter = 0;
int proofStepCounter = 0;

std::vector<std::shared_ptr<NodeEntry>> nodeLog;
std::vector<ProofStepEntry> proofSteps;

std::shared_ptr<NodeEntry> addNode(NodeType type, long long value, std::vector<int> literals, std::vector<int> conflict, long long constraint, std::vector<int> linkedClauses, std::vector<bool> solution) {
    auto node = std::make_shared<NodeEntry>(nodeCounter++, type, value, std::move(literals), std::move(conflict), constraint, std::move(linkedClauses), std::move(solution));
    nodeLog.push_back(node);
    return node;
}

ProofStepEntry& addProofStep(RuleID rule, std::vector<std::vector<int>> premises, std::vector<std::vector<int>> results) {
    ProofStepEntry step(proofStepCounter, rule, std::move(premises), std::move(results));
    proofSteps.push_back(std::move(step));
    std::cout << "Step: " << proofStepCounter << std::endl;
    return proofSteps[proofStepCounter++];
}


////// Plaintext Proof

static std::string toStr(const std::vector<int>& vec) {
    std::ostringstream os;
    os << "[";
    for (size_t i = 0; i < vec.size(); ++i) {
        os << vec[i];
        if (i + 1 < vec.size()) os << ", ";
    }
    os << "]";
    return os.str();
}

static std::string toStrBool(const std::vector<bool>& vec) {
    std::ostringstream os;
    os << "[";
    for (size_t i = 0; i < vec.size(); ++i) {
        os << (vec[i] ? "true" : "false");
        if (i + 1 < vec.size()) os << ", ";
    }
    os << "]";
    return os.str();
}

static std::string toStrNested(const std::vector<std::vector<int>>& vecs) {
    std::ostringstream os;
    os << "[";
    for (size_t i = 0; i < vecs.size(); ++i) {
        os << toStr(vecs[i]);
        if (i + 1 < vecs.size()) os << ", ";
    }
    os << "]";
    return os.str();
}

void exportProofLog(const std::string& filename) {
    std::ofstream out(filename);
    out << "# NODES\n";
    for (const auto& node : nodeLog) {
        out << "NODE " << node->addressID << " type=" << static_cast<int>(node->type);
        if (node->value >= 0) out << " value=" << node->value;
        if (!node->literals.empty()) out << " lits=" << toStr(node->literals);
        if (!node->conflict.empty()) out << " conflict=" << toStr(node->conflict);
        if (node->constraint >= 0) out << " constraint=" << node->constraint;
        if (!node->linkedClauses.empty()) out << " linkedClauses=" << toStr(node->linkedClauses);
        if (!node->solution.empty()) out << " solution=" << toStrBool(node->solution);
        out << "\n";
    }

    out << "# PROOF STEPS\n";
    for (const auto& step : proofSteps) {
        out << "STEP " << step.stepID << " rule=" << static_cast<int>(step.ruleType) << "\n";
        out << "  in=" << toStrNested(step.premiseIDs) << "\n";
        out << "  out=" << toStrNested(step.resultIDs) << "\n";
    }

    out.close();
}


////// ZK Proof Generator

// struct ProofState {
//     int stateID;
//     long long lowerBound;
//     long long upperBound;
//     std::map<int, NodeEntry> hardClausesSet;
//     std::map<int, NodeEntry> softClausesSet;
//     std::map<int, NodeEntry> cardClausesSet;

//     ProofState() = default;

//     ProofState(int id, long long lb, long long ub, std::map<int, NodeEntry> hcs, std::map<int, NodeEntry> scs, std::map<int, NodeEntry> ccs)
//         : stateID(id), lowerBound(lb), upperBound(ub), hardClausesSet(std::move(hcs)), softClausesSet(std::move(scs)), cardClausesSet(std::move(ccs)) {}
// };

// std::map<int, ProofState> proofStatesLog;
// std::vector<protoboard<FieldT>> fullProof;

// void buildZKProofFolder(const std::string& filename) {
//     for (const auto& [id, rule] : ruleLog) {
//         if (id == 1) {
//             protoboard<FieldT> pb = rule1(proofStatesLog[id], proofStatesLog[id+1], rule.clauses);
//         } else if (id == 2) {
//             protoboard<FieldT> pb = rule2(proofStatesLog[id], proofStatesLog[id+1], rule.clauses);
//         } else if (id == 3) {
//             protoboard<FieldT> pb = rule3(proofStatesLog[id], proofStatesLog[id+1], rule.clauses);
//         } else if (id == 4) {
//             protoboard<FieldT> pb = rule4(proofStatesLog[id], proofStatesLog[id+1], rule.clauses);
//         } else if (id == 5) {
//             protoboard<FieldT> pb = rule5(proofStatesLog[id], proofStatesLog[id+1], rule.clauses);
//         }
//         fullProof.insert(pb);
//     }
// }


// // Convert integer to bit vector (little-endian)
// std::vector<bool> int_to_bits(uint64_t val, size_t bits = 256) {
//     std::vector<bool> v(bits, false);
//     for (size_t i = 0; i < bits && val > 0; i++) {
//         v[i] = val & 1;
//         val >>= 1;
//     }
//     return v;
// }

// // Converts a uint64_t to 32-byte (256-bit) buffer
// std::string uint64_to_bytes(uint64_t value) {
//     std::string bytes(32, '\0');
//     for (int i = 0; i < 8; ++i) {
//         bytes[31 - i] = static_cast<char>((value >> (i * 8)) & 0xFF);
//     }
//     return bytes;
// }

// uint64_t generate_nonce() {
//     std::random_device rd;
//     std::mt19937_64 gen(rd());
//     std::uniform_int_distribution<uint64_t> dis;
//     return dis(gen);
// }

// // Compute SHA256(value || nonce) and return as hex string
// std::string sha256_commitment(uint64_t value, uint64_t nonce) {
//     std::string input = uint64_to_bytes(value) + uint64_to_bytes(nonce);

//     unsigned char hash[SHA256_DIGEST_LENGTH];
//     SHA256(reinterpret_cast<const unsigned char*>(input.c_str()), input.size(), hash);

//     std::ostringstream oss;
//     for (int i = 0; i < SHA256_DIGEST_LENGTH; ++i)
//         oss << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(hash[i]);

//     return oss.str(); // hex string of 32 bytes (64 hex chars)
// }

// template<typename FieldT>
// protoboard<FieldT> create_hardening_protoboard(const NodeEntry& soft_clause, const NodeEntry& lb_node, const NodeEntry& ub_node) {
//     protoboard<FieldT> pb;

//     // === Declare variables ===
//     pb_variable<FieldT> lb, ub, weight;
//     pb_variable<FieldT> diff, t, a;
//     pb_variable<FieldT> r_lb, r_ub, r_w;

//     lb.allocate(pb, "LB");
//     ub.allocate(pb, "UB");
//     weight.allocate(pb, "Weight");
//     diff.allocate(pb, "Diff");       // UB - LB
//     t.allocate(pb, "T");             // weight - diff
//     a.allocate(pb, "A");             // t = a^2
//     r_lb.allocate(pb, "R_LB");
//     r_ub.allocate(pb, "R_UB");
//     r_w.allocate(pb, "R_W");

//     // === Commitments ===
//     pb_variable_array<FieldT> commitment_bits; // 3 × 256 = 768 public bits
//     commitment_bits.allocate(pb, 768, "Commitments");

//     pb.set_input_sizes(768); // Public input: 3 hash commitments

//     // === SHA256 commitment inputs ===
//     pb_variable_array<FieldT> lb_bits, ub_bits, w_bits;
//     pb_variable_array<FieldT> r_lb_bits, r_ub_bits, r_w_bits;
//     pb_variable_array<FieldT> input_lb, input_ub, input_w;

//     lb_bits.allocate(pb, 256, "LB_bits");
//     ub_bits.allocate(pb, 256, "UB_bits");
//     w_bits.allocate(pb, 256, "W_bits");
//     r_lb_bits.allocate(pb, 256, "RLB_bits");
//     r_ub_bits.allocate(pb, 256, "RUB_bits");
//     r_w_bits.allocate(pb, 256, "RW_bits");

//     // Concatenate inputs for SHA
//     input_lb.insert(input_lb.end(), lb_bits.begin(), lb_bits.end());
//     input_lb.insert(input_lb.end(), r_lb_bits.begin(), r_lb_bits.end());

//     input_ub.insert(input_ub.end(), ub_bits.begin(), ub_bits.end());
//     input_ub.insert(input_ub.end(), r_ub_bits.begin(), r_ub_bits.end());

//     input_w.insert(input_w.end(), w_bits.begin(), w_bits.end());
//     input_w.insert(input_w.end(), r_w_bits.begin(), r_w_bits.end());

//     // Digest variables (outputs of SHA)
//     digest_variable<FieldT> hash_lb(pb, 256, "hash_lb");
//     digest_variable<FieldT> hash_ub(pb, 256, "hash_ub");
//     digest_variable<FieldT> hash_w(pb, 256, "hash_w");

//     // SHA256 gadgets
//     sha256_two_to_one_hash_gadget<FieldT> sha_lb(pb, input_lb, hash_lb, "sha_lb");
//     sha256_two_to_one_hash_gadget<FieldT> sha_ub(pb, input_ub, hash_ub, "sha_ub");
//     sha256_two_to_one_hash_gadget<FieldT> sha_w(pb, input_w, hash_w, "sha_w");

//     sha_lb.generate_r1cs_constraints();
//     sha_ub.generate_r1cs_constraints();
//     sha_w.generate_r1cs_constraints();

//     // Bind commitment bits to public input
//     for (size_t i = 0; i < 256; ++i) {
//         pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
//             1, hash_lb.bits[i] - commitment_bits[i], 1), "C_lb match");
//         pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
//             1, hash_ub.bits[i] - commitment_bits[256 + i], 1), "C_ub match");
//         pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
//             1, hash_w.bits[i] - commitment_bits[512 + i], 1), "C_w match");
//     }

//     // === Constraints for inequality ===
//     // 1. diff = ub - lb
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, ub - lb, diff), "diff = ub - lb");

//     // 2. t = weight - diff
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, weight - diff, t), "t = weight - diff");

//     // 3. t = a^2 → ensures t ≥ 0
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(a, a, t), "t = a^2");

//     // === Assign witness ===
//     const uint64_t lb_val = lb_node.value;
//     const uint64_t ub_val = ub_node.value;
//     const uint64_t w_val  = soft_clause.value;

//     const uint64_t r_lb_val = generate_nonce();
//     const uint64_t r_ub_val = generate_nonce();
//     const uint64_t r_w_val  = generate_nonce();

//     const uint64_t diff_val = ub_val - lb_val;
//     const int64_t  t_val = static_cast<int64_t>(w_val) - static_cast<int64_t>(diff_val);
//     const uint64_t a_val = static_cast<uint64_t>(sqrt(abs(t_val)));

//     pb.val(lb) = FieldT(lb_val);
//     pb.val(ub) = FieldT(ub_val);
//     pb.val(weight) = FieldT(w_val);
//     pb.val(diff) = FieldT(diff_val);
//     pb.val(t) = FieldT(t_val);
//     pb.val(a) = FieldT(a_val);
//     pb.val(r_lb) = FieldT(r_lb_val);
//     pb.val(r_ub) = FieldT(r_ub_val);
//     pb.val(r_w)  = FieldT(r_w_val);

//     auto assign_bits = [&](auto& arr, auto val) {
//         auto bits = int_to_bits(val);
//         for (size_t i = 0; i < 256; ++i)
//             pb.val(arr[i]) = bits[i] ? FieldT::one() : FieldT::zero();
//     };

//     assign_bits(lb_bits, lb_val);
//     assign_bits(r_lb_bits, r_lb_val);
//     assign_bits(ub_bits, ub_val);
//     assign_bits(r_ub_bits, r_ub_val);
//     assign_bits(w_bits, w_val);
//     assign_bits(r_w_bits, r_w_val);

//     sha_lb.generate_r1cs_witness();
//     sha_ub.generate_r1cs_witness();
//     sha_w.generate_r1cs_witness();

//     for (size_t i = 0; i < 256; ++i) {
//         pb.val(commitment_bits[i]) = pb.val(hash_lb.bits[i]);
//         pb.val(commitment_bits[256 + i]) = pb.val(hash_ub.bits[i]);
//         pb.val(commitment_bits[512 + i]) = pb.val(hash_w.bits[i]);
//     }

//     assert(pb.is_satisfied());

//     // Compute real-world hex commitments using your helper
//     std::string C_lb = sha256_commitment(lb_val, r_lb_val);
//     std::string C_ub = sha256_commitment(ub_val, r_ub_val);
//     std::string C_w  = sha256_commitment(w_val,  r_w_val);

//     assert(pb.is_satisfied());

//     return {pb, C_lb, C_ub, C_w};
// }

// template<typename FieldT>
// std::tuple<protoboard<FieldT>, std::string>
// create_minimum_proof(
//     const std::vector<long long>& values,
//     long long claimed_min,
//     const std::vector<uint64_t>& value_nonces,
//     uint64_t min_nonce
// ) {
//     protoboard<FieldT> pb;

//     const size_t n = values.size();
//     assert(value_nonces.size() == n);

//     // === Allocate variables ===
//     pb_variable<FieldT> min_var;
//     min_var.allocate(pb, "min");

//     pb_variable<FieldT> min_nonce_var;
//     min_nonce_var.allocate(pb, "r_min");

//     pb_variable_array<FieldT> min_bits, nonce_bits, hash_bits;
//     min_bits.allocate(pb, 256, "min_bits");
//     nonce_bits.allocate(pb, 256, "nonce_bits");

//     pb_variable_array<FieldT> min_input;
//     min_input.insert(min_input.end(), min_bits.begin(), min_bits.end());
//     min_input.insert(min_input.end(), nonce_bits.begin(), nonce_bits.end());

//     digest_variable<FieldT> hash_result(pb, 256, "hash_min");
//     sha256_two_to_one_hash_gadget<FieldT> sha_min(pb, min_input, hash_result, "sha_min");

//     pb_variable_array<FieldT> commitment_bits;
//     commitment_bits.allocate(pb, 256, "C_min");
//     pb.set_input_sizes(256); // public input is C_min

//     sha_min.generate_r1cs_constraints();

//     for (size_t i = 0; i < 256; ++i) {
//         pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
//             1, hash_result.bits[i] - commitment_bits[i], 1));
//     }

//     // === Constraints to prove min ===
//     std::vector<pb_variable<FieldT>> s_vars;
//     std::vector<pb_variable<FieldT>> a_vars;
//     std::vector<pb_variable<FieldT>> is_equal;

//     for (size_t i = 0; i < n; ++i) {
//         pb_variable<FieldT> s;
//         pb_variable<FieldT> a;
//         pb_variable<FieldT> eq;

//         s.allocate(pb, "s_" + std::to_string(i));
//         a.allocate(pb, "a_" + std::to_string(i));
//         eq.allocate(pb, "is_equal_" + std::to_string(i));

//         s_vars.push_back(s);
//         a_vars.push_back(a);
//         is_equal.push_back(eq);

//         // sᵢ - min = aᵢ² → sᵢ ≥ min
//         pb.add_r1cs_constraint(r1cs_constraint<FieldT>(a, a, s - min_var),
//                                "s_i - min = a_i^2");

//         // Equality check: (sᵢ - min) * eq = 0
//         // If sᵢ == min → (0) * eq = 0 → ok
//         // If sᵢ != min → eq must be 0
//         pb.add_r1cs_constraint(r1cs_constraint<FieldT>(
//             s - min_var, eq, 0), "eq * diff = 0");
//     }

//     // === Enforce that at least one eqᵢ is 1
//     pb_variable<FieldT> sum_eq;
//     sum_eq.allocate(pb, "sum_eq");

//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sum_eq - std::accumulate(is_equal.begin(), is_equal.end(), pb_variable<FieldT>(), [](auto acc, auto x) { return acc + x; }), 0),
//                            "sum_eq = sum(eq_i)");

//     // For hard enforcing ≥ 1, we prove:
//     // exists i where eqᵢ = 1 → we constrain sum_eq >= 1
//     // via: sum_eq - 1 = b² → b² ≥ 0
//     pb_variable<FieldT> nonneg_b;
//     nonneg_b.allocate(pb, "b");
//     pb.add_r1cs_constraint(r1cs_constraint<FieldT>(nonneg_b, nonneg_b, sum_eq - 1), "sum_eq - 1 = b²");

//     // === Assign witness values ===
//     pb.val(min_var) = FieldT(claimed_min);
//     pb.val(min_nonce_var) = FieldT(min_nonce);

//     auto assign_bits = [&](pb_variable_array<FieldT>& arr, uint64_t val) {
//         auto bits = int_to_bits(val);
//         for (size_t i = 0; i < 256; ++i)
//             pb.val(arr[i]) = bits[i] ? FieldT::one() : FieldT::zero();
//     };

//     assign_bits(min_bits, claimed_min);
//     assign_bits(nonce_bits, min_nonce);

//     for (size_t i = 0; i < n; ++i) {
//         long long s_i = values[i];
//         pb.val(s_vars[i]) = FieldT(s_i);

//         long long a_i = static_cast<long long>(sqrt(abs(s_i - claimed_min)));
//         pb.val(a_vars[i]) = FieldT(a_i);

//         pb.val(is_equal[i]) = (s_i == claimed_min) ? FieldT::one() : FieldT::zero();
//     }

//     // Compute b = sqrt(sum_eq - 1)
//     long long sum_eq_val = std::accumulate(values.begin(), values.end(), 0, [&](int acc, long long v) {
//         return acc + ((v == claimed_min) ? 1 : 0);
//     });

//     pb.val(sum_eq) = FieldT(sum_eq_val);
//     pb.val(nonneg_b) = FieldT(static_cast<uint64_t>(sqrt(sum_eq_val - 1)));

//     sha_min.generate_r1cs_witness();

//     for (size_t i = 0; i < 256; ++i) {
//         pb.val(commitment_bits[i]) = pb.val(hash_result.bits[i]);
//     }

//     assert(pb.is_satisfied());

//     std::string C_min = sha256_commitment(claimed_min, min_nonce);
//     return {pb, C_min};
// }
