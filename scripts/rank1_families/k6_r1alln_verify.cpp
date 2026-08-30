#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using std::array;
using std::cerr;
using std::cout;
using std::string;
using std::vector;

struct Candidate {
    int omitted;              // 0 = c_0, 1..m = ordinary column
    vector<int> tau;          // tau[r] is the column label placed in matrix column r
    string kind;
};

static int mod_pow(int a, int e, int p) {
    long long r = 1, b = ((a % p) + p) % p;
    while (e) {
        if (e & 1) r = r * b % p;
        b = b * b % p;
        e >>= 1;
    }
    return (int)r;
}

static bool is_prime(int p) {
    if (p < 2) return false;
    for (int d = 2; 1LL * d * d <= p; ++d) if (p % d == 0) return false;
    return true;
}

static vector<vector<int>> all_permutations(int m) {
    vector<int> v(m);
    std::iota(v.begin(), v.end(), 0);
    vector<vector<int>> out;
    do { out.push_back(v); } while (std::next_permutation(v.begin(), v.end()));
    return out;
}

static vector<Candidate> make_candidates(int m, const string& mode) {
    vector<Candidate> out;
    vector<int> base(m);
    std::iota(base.begin(), base.end(), 0);

    if (mode == "all") {
        for (int j = 0; j <= m; ++j) {
            vector<int> rest;
            for (int k = 0; k <= m; ++k) if (k != j) rest.push_back(k);
            do {
                out.push_back({j, rest, "all"});
            } while (std::next_permutation(rest.begin(), rest.end()));
        }
        return out;
    }
    if (mode != "restricted") throw std::runtime_error("mode must be all or restricted");

    // Omit c_0 and use an m-cycle.  Fix the first vertex to avoid rotational duplicates.
    if (m == 1) {
        out.push_back({0, vector<int>{1}, "c0-cycle"});
    } else {
        vector<int> tail;
        for (int k = 1; k < m; ++k) tail.push_back(k);
        do {
            vector<int> cyc{0};
            cyc.insert(cyc.end(), tail.begin(), tail.end());
            vector<int> tau(m, -1);
            for (int r = 0; r < m; ++r) {
                int from = cyc[r], to = cyc[(r + 1) % m];
                tau[from] = to + 1;
            }
            out.push_back({0, tau, "c0-cycle"});
        } while (std::next_permutation(tail.begin(), tail.end()));
    }

    // Omit the first vertex of a Hamilton path ending in c_0.
    auto perms = all_permutations(m);
    for (const auto& v : perms) {
        vector<int> tau(m, -1);
        for (int r = 0; r + 1 < m; ++r) tau[v[r]] = v[r + 1] + 1;
        tau[v[m - 1]] = 0;
        out.push_back({v[0] + 1, tau, "path"});
    }

    // One fixed ordinary vertex, with a Hamilton path on the complement ending in c_0.
    if (m >= 2) {
        for (int f = 0; f < m; ++f) {
            vector<int> rest;
            for (int k = 0; k < m; ++k) if (k != f) rest.push_back(k);
            do {
                vector<int> tau(m, -1);
                tau[f] = f + 1;
                for (int r = 0; r + 1 < (int)rest.size(); ++r)
                    tau[rest[r]] = rest[r + 1] + 1;
                tau[rest.back()] = 0;
                out.push_back({rest[0] + 1, tau, "path+fixed"});
            } while (std::next_permutation(rest.begin(), rest.end()));
        }
    }
    return out;
}

static bool cyclic_pair(const vector<vector<int>>& columns,
                        const Candidate& cand, int p, int m) {
    // M is stored by columns; K stores b, Mb, ..., M^(m-1)b by columns.
    vector<vector<int>> M(m, vector<int>(m));
    for (int c = 0; c < m; ++c)
        for (int r = 0; r < m; ++r)
            M[r][c] = columns[cand.tau[c]][r];

    vector<vector<int>> K(m, vector<int>(m));
    vector<int> v = columns[cand.omitted], nv(m);
    for (int c = 0; c < m; ++c) {
        for (int r = 0; r < m; ++r) K[r][c] = v[r];
        std::fill(nv.begin(), nv.end(), 0);
        for (int r = 0; r < m; ++r) {
            long long s = 0;
            for (int k = 0; k < m; ++k) s += 1LL * M[r][k] * v[k];
            nv[r] = (int)(s % p);
        }
        v.swap(nv);
    }

    // Exact Gaussian rank over F_p.
    int rank = 0;
    for (int c = 0; c < m; ++c) {
        int piv = -1;
        for (int r = rank; r < m; ++r) if (K[r][c] % p != 0) { piv = r; break; }
        if (piv < 0) continue;
        std::swap(K[piv], K[rank]);
        int inv = mod_pow(K[rank][c], p - 2, p);
        for (int k = c; k < m; ++k) K[rank][k] = (int)(1LL * K[rank][k] * inv % p);
        for (int r = 0; r < m; ++r) if (r != rank && K[r][c]) {
            int q = K[r][c];
            for (int k = c; k < m; ++k) {
                K[r][k] = (K[r][k] - (int)(1LL * q * K[rank][k] % p)) % p;
                if (K[r][k] < 0) K[r][k] += p;
            }
        }
        if (++rank == m) return true;
    }
    return false;
}

static vector<int> decode(uint64_t code, int p, int m) {
    vector<int> a(m);
    for (int i = 0; i < m; ++i) { a[i] = (int)(code % p); code /= p; }
    return a;
}

static uint64_t ipow_u64(uint64_t a, int e) {
    uint64_t r = 1;
    while (e--) {
        if (r > UINT64_MAX / a) throw std::overflow_error("state count overflow");
        r *= a;
    }
    return r;
}

static vector<vector<int>> make_columns(const vector<int>& x, const vector<int>& y, int p) {
    int m = (int)x.size();
    vector<vector<int>> c(m + 1, vector<int>(m));
    c[0] = x;
    for (int k = 0; k < m; ++k)
        for (int r = 0; r < m; ++r)
            c[k + 1][r] = ((r == k ? 1 : 0) + y[k] * x[r]) % p;
    return c;
}

static void print_vec(const vector<int>& a) {
    cout << '[';
    for (int i = 0; i < (int)a.size(); ++i) { if (i) cout << ','; cout << a[i]; }
    cout << ']';
}

int main(int argc, char** argv) {
    if (argc != 4) {
        cerr << "usage: " << argv[0] << " PRIME_P M MODE(all|restricted)\n";
        return 2;
    }
    int p = std::stoi(argv[1]), m = std::stoi(argv[2]);
    string mode = argv[3];
    if (!is_prime(p) || m < 1 || m > 9) {
        cerr << "Require prime p and 1 <= m <= 9.\n";
        return 2;
    }

    auto candidates = make_candidates(m, mode);
    vector<int> c0_idx, other_idx;
    for (int i = 0; i < (int)candidates.size(); ++i) {
        if (candidates[i].omitted == 0) c0_idx.push_back(i); else other_idx.push_back(i);
    }

    uint64_t qpow = ipow_u64((uint64_t)p, m);
    uint64_t total_pairs = qpow * qpow;
    uint64_t x_solved_by_c0 = 0, residual_pairs = 0, witness_checks = 0;
    uint64_t max_checks = 0;
    vector<int> hardest_x, hardest_y;
    Candidate hardest_cand;
    bool have_hard = false;

    auto t0 = std::chrono::steady_clock::now();
    for (uint64_t xc = 0; xc < qpow; ++xc) {
        vector<int> x = decode(xc, p, m), zero_y(m, 0);
        auto cols0 = make_columns(x, zero_y, p);
        bool c0_good = false;
        for (int idx : c0_idx) {
            ++witness_checks;
            if (cyclic_pair(cols0, candidates[idx], p, m)) { c0_good = true; break; }
        }
        if (c0_good) {
            ++x_solved_by_c0;
            continue;  // feedback lemma makes this independent of y
        }

        for (uint64_t yc = 0; yc < qpow; ++yc) {
            ++residual_pairs;
            vector<int> y = decode(yc, p, m);
            auto cols = make_columns(x, y, p);
            uint64_t local = 0;
            bool good = false;
            Candidate winner;
            for (int idx : other_idx) {
                ++local; ++witness_checks;
                if (cyclic_pair(cols, candidates[idx], p, m)) {
                    good = true; winner = candidates[idx]; break;
                }
            }
            if (!good) {
                cout << "COUNTEREXAMPLE p=" << p << " m=" << m << " mode=" << mode << " x=";
                print_vec(x); cout << " y="; print_vec(y); cout << "\n";
                return 1;
            }
            if (local > max_checks) {
                max_checks = local; hardest_x = x; hardest_y = y; hardest_cand = winner; have_hard = true;
            }
        }
    }
    auto t1 = std::chrono::steady_clock::now();
    double sec = std::chrono::duration<double>(t1 - t0).count();

    cout << "PROVED_BY_EXHAUSTION"
         << " p=" << p << " m=" << m << " n=" << (m + 1)
         << " mode=" << mode
         << " candidates=" << candidates.size()
         << " total_pairs=" << total_pairs
         << " x_solved_by_c0=" << x_solved_by_c0
         << " residual_pairs_checked=" << residual_pairs
         << " witness_checks=" << witness_checks
         << " max_residual_checks=" << max_checks
         << " seconds=" << sec << "\n";
    if (have_hard) {
        cout << "HARDEST x="; print_vec(hardest_x); cout << " y="; print_vec(hardest_y);
        cout << " winner_kind=" << hardest_cand.kind << " omitted=" << hardest_cand.omitted << " tau=";
        print_vec(hardest_cand.tau); cout << "\n";
    }
    return 0;
}
