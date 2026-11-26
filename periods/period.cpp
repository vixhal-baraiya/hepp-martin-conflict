// Period of a primitive log-divergent phi^4 graph (decompleted), by tropical Monte Carlo
// (M. Borinsky, tropical-feynman-quadrature). Build inside a checkout of that repository.
// usage: period <graphfile> <samples_per_batch> <batches> <seed>
// graphfile: "V E" then E lines "u v" (0-based vertices).
// Prints one independent estimate per batch; combine them with combine.py. (The library's own
// running statistics overflow beyond 2^32 samples, so no running total is printed.)
#include <iostream>
#include <fstream>
#include <chrono>
#include <omp.h>
#include <stdexcept>
#include <vector>
#include <tuple>
#include <sstream>
using namespace std;
#include "graph.hpp"
#include "subgraph_table.hpp"
#include "feynman_integral.hpp"

static vector<Eigen::VectorXd> sym_momenta(int V) {
    vector<Eigen::VectorXd> m(V);
    for (int i = 0; i < V; i++) { m[i].setZero(V); for (int j = 0; j < V; j++) m[i][j] = (i == j) ? V - 1. : -1.; }
    return m;
}

int main(int argc, char **argv) {
    if (argc < 5) { cerr << "usage: period <graphfile> <samples_per_batch> <batches> <seed>" << endl; return 1; }
    ifstream in(argv[1]); int V, E; in >> V >> E;
    graph::edge_vector ev;
    for (int i = 0; i < E; i++) { int a, b; in >> a >> b; ev.push_back(graph::edge_tuple{{a, b}, 1}); }
    graph g(ev);
    uint64_t N = strtoull(argv[2], 0, 10); int B = atoi(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
    const int D = 4;
    auto mom = sym_momenta(g._V);                        // the period does not depend on external data
    Eigen::VectorXd sig = Eigen::VectorXd::Constant(mom[0].size(), -1.0);
    vector<double> m2(g._E, 0.0);                        // massless
    J_vector table; int W; double IGtr;
    tie(table, W, IGtr) = generate_subgraph_table(g, D, mom, m2, sig, 1e-10);
    cout << "W=" << W << " Itr=" << IGtr << " threads=" << omp_get_max_threads() << endl;
    true_random::xoshiro256 gen(seed);
    for (int b = 0; b < B; b++) {
        auto s0 = chrono::system_clock::now();
        stats r = feynman_integral_estimate(N, g, D, mom, m2, sig, table, gen);
        for (int k = 0; k < 8; k++) gen.jump();
        printf("batch %d  N=%.3g  batch %.10g +- %.4g | %.1f s\n", b, (double)N, r.avg(), r.acc(),
               chrono::duration<double>(chrono::system_clock::now() - s0).count());
        fflush(stdout);
    }
    return 0;
}
