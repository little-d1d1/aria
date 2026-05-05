#include <fstream>
#include <iostream>
#include <Eigen/Dense>
#include <cmath>
#include "misc.h"
#include "random.hpp"
#include "random/uniform_int.hpp"
#include "random/normal_distribution.hpp"
#include "random/uniform_real_distribution.hpp"

#include "random_walks/random_walks.hpp"
// #include "random_walks/multithread_walks.hpp"

#include "volume/volume_sequence_of_balls.hpp"
#include "known_polytope_generators.h"
// #include "sampling/random_point_generators_multithread.hpp"

#include "diagnostics/univariate_psrf.hpp"


// Define types
typedef double NT; // Number type
typedef Eigen::Matrix<NT,Eigen::Dynamic,Eigen::Dynamic> MT;
// typedef Cartesian<NT> Kernel;  // Kernel (Cartesian coordinate system)
// typedef typename Kernel::Point Point;  // Point type
// typedef Eigen::Matrix<NT, Eigen::Dynamic, Eigen::Dynamic> MT;  // Matrix type for Eigen
// typedef HPolytope<Point, MT> HPolytope;  // Correctly specify the polytope type
// typedef BoostRandomNumberGenerator<boost::mt19937, NT, 3> RNGType;
    typedef BoostRandomNumberGenerator<boost::mt19937, NT, 3> RNGType;


typedef Cartesian<NT>    Kernel;
typedef typename Kernel::Point    Point;
typedef HPolytope<Point> Hpolytope;
typedef Eigen::Matrix<NT,Eigen::Dynamic,Eigen::Dynamic> MT;
typedef Eigen::Matrix<NT,Eigen::Dynamic,1> VT;

// Function to find the nearest lattice point inside the polytope
Point findAnyLatticePoint(const Hpolytope &polytope, const Point &point) {
    unsigned int d = point.dimension();
    Eigen::VectorXd coords(d);

    // Generate a lattice point by flooring each dimension
    for (unsigned int j = 0; j < d; ++j) {
        coords(j) = std::floor(point.getCoefficients()(j));
    }

    Point candidate(coords);
    if (polytope.is_in(candidate)) {
        return candidate;
    }

    // Try all combinations of floor and ceiling for each dimension
    for (unsigned int i = 0; i < (1 << d); ++i) {
        for (unsigned int j = 0; j < d; ++j) {
            if (i & (1 << j)) {
                coords(j) = std::ceil(point.getCoefficients()(j));
            } else {
                coords(j) = std::floor(point.getCoefficients()(j));
            }
        }
        candidate = Point(coords);
        if (polytope.is_in(candidate)) {
            return candidate;
        }
    }

    // If no lattice point is found, return the original point
    return NULL;
}

template <typename WalkType>
void samplePolytope(Hpolytope &polytope, unsigned int walk_len, unsigned int N, unsigned int num_threads, MT &samples, bool verbose = false) {
    RNGType rng(polytope.dimension());  // Random number generator
    typedef typename WalkType::template Walk<Hpolytope, RNGType> walk;  // Define the walk type
    PushBackWalkPolicy push_back_policy;  // Policy to manage generated points
    // Print the polytope

    // Compute the starting point (inner ball center)
    auto start = std::chrono::high_resolution_clock::now();
    Point p = polytope.ComputeInnerBall().first;
    auto end = std::chrono::high_resolution_clock::now();
    std::chrono::duration<double> elapsed = end - start;
    // std::cout << "Inner ball center: (dim =" << p.dimension() <<  ")"  << std::endl;
    // for (int i = 0; i < p.dimension(); i++) {
    //     std::cout << p.getCoefficients()(i) << " ";
    // }
    double kv_radius = sqrt(std::log(polytope.num_of_hyperplanes()))*p.dimension();
    std::cout << "c [ttc->volesti] KV97 condition radius " << kv_radius << " (" << p.dimension() << " dimension, " << polytope.num_of_hyperplanes() << " facets)" << std::endl;
    std::cout << "c [ttc->volesti] Chebyshev radius: " << polytope.ComputeInnerBall().second << std::endl;
    std::cout << "c [ttc->volesti] radius calculation time: " << elapsed.count() << " seconds" << std::endl;
    if (N == 0) {
        return;
    }
    // print p

    // List to store random points
    std::list<Point> randPoints;

    // Define the random point generator with multi-threading
    typedef RandomPointGenerator<walk> RandomPointGenerator;
    RandomPointGenerator::apply(polytope, p, N, walk_len, randPoints, push_back_policy, rng);

    // Prepare the samples matrix
    unsigned int d = p.dimension();  // Dimension of the polytope

    // MT samples(d, N);
    unsigned int jj = 0;

    for (typename std::list<Point>::iterator rpit = randPoints.begin(); rpit!=randPoints.end(); rpit++, jj++)
    {
        samples.col(jj) = (*rpit).getCoefficients();
        std::cout << "Sampled point: " ;
    for (unsigned int k = 0; k < d; k++) {
        std::cout << (*rpit).getCoefficients()(k) << " ";
    }
    std::cout << std::endl;
    Point nearest_lattice_point = findAnyLatticePoint(polytope, *rpit);
    std::cout << "Nearest lattice point: ";
    for (unsigned int k = 0; k < d; k++) {
        std::cout << nearest_lattice_point.getCoefficients()(k) << " ";
    }
    std::cout << std::endl;

    }

}




// Function to load the polytope from file
// Function to load polytope from file
Hpolytope loadPolytope(const std::string &filename) {
    std::ifstream file(filename);
    if (!file) {
        throw std::runtime_error("Could not open file: " + filename);
    }

    unsigned int m, n;
    file >> m >> n; // h-poytope size (m x n) -- number of inequalities and variables +1

    Eigen::MatrixXd matrix(m, n);
    for (unsigned int i = 0; i < m; ++i) {
        for (unsigned int j = 0; j < n ; ++j) {
            if (j == 0)
                file >>  matrix(i, j);
            else
                file >> matrix(i, j);
        }
    }

    // Extract \(b\) and \(-A\) from the matrix \([b | -A]\)
    Eigen::VectorXd b = matrix.col(0);
    Eigen::MatrixXd A = matrix.block(0, 1, m, n-1);

    // Construct the polytope
    return Hpolytope(n, A, b); // Use dimension \(n\), matrix \(A\), and vector \(b\)
}


// Main function
int main(int argc, char *argv[]) {
    if (argc != 2 && argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <input_file> [<num_samples>]" << std::endl;
        return 1;
    }

    std::string input_file = argv[1];
    unsigned int num_samples = 0;
    if (argc == 2){
        num_samples = 0;
    } else {
     num_samples = std::stoi(argv[2]);
    }
    try {
        // Load the polytope
        Hpolytope polytope = loadPolytope(input_file);

        // Sampling parameters
        unsigned int walk_len = 100;
        unsigned int num_threads = 1;

        // Perform sampling
        MT samples;
        typedef BilliardWalk WalkType;

        samplePolytope<WalkType>(polytope, walk_len, num_samples, num_threads, samples);
        // get size of samples

        // Output the samples
        for (int i = 0; i < samples.rows(); i++) {
            for (int j = 0; j < samples.cols(); j++) {
                std::cout << samples(i, j) << " ";
            }
            std::cout << std::endl;
        }
    } catch (const std::exception &e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}