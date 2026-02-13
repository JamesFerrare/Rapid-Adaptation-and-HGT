#include <iostream>
#include <vector>
#include <cmath>
#include <cstdlib>
#include <ctime>
#include <random>
#include <algorithm>
#include <numeric>
#include <fstream>
#include <chrono>
#include <unordered_set>
#include <sstream>
#include <chrono>
#include <iomanip>

// Function to initialize arrays
void initializeArrays(int* arr, int size) {
    for (int i = 0; i < size; i++) {
        arr[i] = 0;
    }
}

void initializeArraysDouble(double* arr, int size) {
    for (int i = 0; i < size; i++) {
        arr[i] = 0.0;
    }
}

void initializeArraysBool(bool* arr, int size) {
    for (int i = 0; i < size; i++) {
        arr[i] = 0;
    }
}

//Wright-fisher simulation with recombination
int evolve(double mu, double N, int L, double s1, double s2, double U1, double U2, double U1_m, double U2_m, double s1_m, double s2_m, double r, double r_m, int transfer_length, int recombination_type,int num_beneficial_loci) {

    //ARRAY SIZES
    int MAX_SIZE=200000000;
    int MAX_POLY=70;

    //SIMULATION DURATION
    int tmax=5000; //number of generations
    //double Tc=((1 / s1) * log(s1 / U1));
    //int tmax= static_cast<int>(round(50 * Tc));
    int teq=2000; //number of generations to reach equilibrium
    int teq = static_cast<int>(round(10 * Tc));

    //DEFINE VARIABLES
    double Um=0; //rate of modifiers being introduced after equilibrium
    int tfix=0; //time to fixation of modifier
    double X_final=0; //fitness of population
    double population_size; //population size
    double population_size_non_modifier=N; //population size of non-modifier lineages
    double population_size_modifier=0; //population size of modifier lineages
    int num_neutral_modifier_mutants=0; //number of new neutral modifier mutations
    int num_beneficial_mutants=0; //number of new beneficial mutations
    int num_beneficial_modifier_mutants=0; //number of new beneficial modifier mutations
    int background=1; //sampled genetic background
    double mean_fitness=0; //mean fitness of population
    int start_location=1; //start location of transferred region
    int end_location=2; //end location of transferred region
    int num_recombinants=0; //number of new recombinants
    int num_modifier_recombinants=0; //number of new recombinants in modifier lineages
    int is_non_modifier_acceptor_or_donor;
    int is_modifier_acceptor_or_donor;
    int acceptor;
    int donor;
    int who_is_donor;
    int who_is_acceptor;
    int polymorphism_to_remove;
    int num_fixed_mutations=0;
    bool permutation=false;
    int permutation_index;
    bool modifier_is_acceptor=false;
    bool non_modifier_is_donor=false;
    bool modifier_is_donor=false;
    bool non_modifier_is_acceptor=false;
    bool in_all_rows=false;
    int location;
    double norm;
    bool is_removed_site_recombined=false;
    int total_fixations =0;
    int recombined_fixations=0;
    bool mismatch=true;
    bool reversion=true;
    int max_column;
    int number_recomb_events_viable=0;
    double max_fitness=0;


    //DEFINE ARRAY VARIABLES
    double* lineage_sizes = new double[MAX_SIZE];
    double* lineage_sizes_modifier = new double[MAX_SIZE];
    double* expected_lineage_sizes = new double[MAX_SIZE];
    double* expected_lineage_sizes_modifier = new double[MAX_SIZE];
    double* sizes = new double[MAX_SIZE];
    double* sizes_modifier = new double[MAX_SIZE];
    double* lineage_fitnesses = new double[MAX_SIZE];
    int* next_column1= new int[MAX_SIZE];
    int* beneficial_loci = new int[num_beneficial_loci];

    // Dynamically allocate memory for 2D arrays on the heap
    int** polymorphic_sites = new int*[MAX_SIZE];
    for (int i = 0; i < MAX_SIZE; i++) {
        polymorphic_sites[i] = new int[MAX_POLY];
    }
    
    bool** is_site_recombined = new bool*[MAX_SIZE];
    for (int i = 0; i < MAX_SIZE; i++) {
        is_site_recombined[i] = new bool[MAX_POLY];
    }

    // Initialize arrays
    initializeArraysDouble(lineage_sizes, MAX_SIZE);
    initializeArraysDouble(lineage_sizes_modifier, MAX_SIZE);
    initializeArraysDouble(expected_lineage_sizes, MAX_SIZE);
    initializeArraysDouble(expected_lineage_sizes_modifier, MAX_SIZE);
    initializeArraysDouble(sizes, MAX_SIZE);
    initializeArraysDouble(sizes_modifier, MAX_SIZE);
    initializeArraysDouble(lineage_fitnesses, MAX_SIZE);
    initializeArrays(next_column1, MAX_SIZE);


    // Initialize 2D arrays
    for (int i = 0; i < MAX_SIZE; i++) {
        initializeArrays(polymorphic_sites[i], MAX_POLY);
    }
    lineage_sizes[0]=N;

    for (int i = 0; i < MAX_SIZE; i++) {
        initializeArraysBool(is_site_recombined[i], MAX_POLY);
    }

    //vector to store which sites are polymorphic
    //std::unordered_set<int> polymorphic_sites_population;

    //vector of overlap in recombined genomes
    std::vector<int> donor_acceptor_diff={};

    //vector of indices transferred in recombination event
    std::vector<int> acceptor_sites= {};
    std::vector<int> donor_sites = {};

    //vector of polymorhisms transferred in recombination event
    std::vector<int> acceptor_poly= {};
    std::vector<int> donor_poly = {};
    
    
    //vector to store the order of polymorphic sites in a lineage
    std::vector<int> permuted_order = {};

    //vectors to check for duplicates
    std::vector<int> check_identical_focal = {};
    std::vector<int> check_identical_replace = {};

    //vector to track fixed polymorphisms
    std::vector<int> fixed_polymorphisms = {};

    //Seed generation using a combination of time and random_device
    unsigned seed = static_cast<unsigned>(
        std::chrono::system_clock::now().time_since_epoch().count());
    std::random_device rd;
    seed ^= rd() + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    std::mt19937 generator(seed);
    //print seed
    std::cout << "Seed: " << seed << std::endl;

    //start a timer
    auto start_time = std::chrono::steady_clock::now();
    

    //index variables
    int nextrow=1; //index of next new background beneficial lineage
    int nextrow_old=1;
    
    //define distributions
    std::uniform_int_distribution<int> distribution(1, L);
    std::uniform_int_distribution<int> distribution_ben_loc(1, num_beneficial_loci);
    std::uniform_int_distribution<int> donor_or_acceptor(0, 1);
    std::uniform_int_distribution<int> distribution_r(1, L);
    std::poisson_distribution<long long> poisson_sample;
    std::discrete_distribution<int> sample_lineage; //distribution of lineages weighted by their size
    std::discrete_distribution<int> sample_lineage_modifier; //distribution of modifier lineages weighted by their size
    std::binomial_distribution<int> number_of_mutations;
    std::binomial_distribution<int> number_of_recombinants;
    std::poisson_distribution<int> number_of_mutations_poisson;
    std::poisson_distribution<int> number_of_recombinants_poisson;
    std::bernoulli_distribution sample;

    // Sample beneficial loci but do not allow L/2
    for (int i = 0; i < num_beneficial_loci; i++) {
        bool new_locus = false;
        int new_locus_value=L/2;
        while (!new_locus) {
            // Generate a new locus
            new_locus_value = distribution(generator);

            // Ensure it's not L/2 and not already chosen
            if (new_locus_value != L/2 && 
                std::find(beneficial_loci, beneficial_loci + num_beneficial_loci, new_locus_value) == beneficial_loci + num_beneficial_loci) {
                beneficial_loci[i] = new_locus_value;
                new_locus = true;
            }
        }
    }

    //define variable q=2*ln(N*s1)/ln(s1/Ub)
    double q=2*log(N*s1)/log(s1/U1);
    //print q
    std::cout << "q: " << q << std::endl;
    //define variabl eta = absolute value ln(q*transfer_length/L)
    double eta=log(s1/U1)/abs(log(transfer_length/L));
    //print eta
    std::cout << "eta: " << eta << std::endl;
    //print r*(l/L)/Ub
    std::cout << "r*l/Ub: " << r*static_cast<double>(transfer_length)/static_cast<double>(L)/U1 << std::endl;
    // print N
    std::cout << "N: " << N << std::endl;
    //print Ub
    std::cout << "Ub: " << U1 << std::endl;
    //print s1
    std::cout << "s1: " << s1 << std::endl;
    //print r
    std::cout << "r: " << r/L << std::endl;
    //print r_m
    std::cout << "r_m: " << r_m/L << std::endl;

    //std::vector<int> sites_that_fixed = {390046, 522989, 830976, 966910, 731361, 799347, 370095, 309545, 908914, 459631, 583328, 881132, 551810, 149927, 591431, 190606, 343261, 152411, 483559, 263560, 615068, 288043, 653142, 914686, 725416, 940396, 128447, 93244, 306394, 911669, 14129, 871407, 243176, 933304, 711642, 475604, 878543, 71387, 861701, 365736, 158083, 404210, 79537, 38566, 834672, 871195, 674171, 109160, 896024, 544163, 816297, 730609, 633500, 566843, 690462, 597668, 908914, 425576, 645090, 913056, 249263,476825, 510954};
    //bulk_size_sites_that_fixed is vector of zeros with number elements equal to length of sites_that_fixed

    //iterate over t generations
    for (int t=0; t<tmax+teq; t++) {
        if (t==teq) {
            X_final=0;
            Um=mu;
            recombined_fixations=0;
            total_fixations=0;
            fixed_polymorphisms.clear();
        }
        nextrow_old = nextrow;
        //max fitness equals maximum value of lineage_fitnesses
        //max_fitness = *std::max_element(lineage_fitnesses, lineage_fitnesses + nextrow);

        //calculate row with most non-zero elements
        //*std::max_element(next_column1, next_column1 + nextrow);
        //print lineage_sizes

        //Calculate population size by summing lineage sizes and modifier lineage sizes
        population_size=0;
        for (int i = 0; i < nextrow; i++) {
            population_size += exp(lineage_fitnesses[i]) * (lineage_sizes[i]+lineage_sizes_modifier[i]);

        }
        norm=N / population_size;

        // // DETERMINISTIC GROWTH
        for (int i = 0; i < nextrow; i++) {
            expected_lineage_sizes[i] = exp(lineage_fitnesses[i]) * (lineage_sizes[i]) * norm;
            expected_lineage_sizes_modifier[i] = exp(lineage_fitnesses[i]) * (lineage_sizes_modifier[i]) * norm;
        }

        // RANDOM POISSON SAMPLING
        for (int i = 0; i < nextrow; i++) {
                poisson_sample.param(std::poisson_distribution<long long>::param_type((1.0 - U1 - U2 - Um)*expected_lineage_sizes[i]));
                sizes[i] = static_cast<double>(poisson_sample(generator));
                poisson_sample.param(std::poisson_distribution<long long>::param_type((1.0 - U1_m - U2_m)*expected_lineage_sizes_modifier[i]));
                sizes_modifier[i] = static_cast<double>(poisson_sample(generator));
        }

        //MUTATION

        // How many new mutations and where are locations along genome
        population_size_non_modifier=std::accumulate(expected_lineage_sizes, expected_lineage_sizes+nextrow, 0.0); //population size of non-modifier lineages
        population_size_modifier=std::accumulate(expected_lineage_sizes_modifier, expected_lineage_sizes_modifier+ nextrow, 0.0); //population size of modifier lineages
        
        //update sample lineage parameters
        sample_lineage.param(std::discrete_distribution<int>::param_type(lineage_sizes, lineage_sizes+nextrow)); //distribution of lineages weighted by their size
        sample_lineage_modifier.param(std::discrete_distribution<int>::param_type(lineage_sizes_modifier, lineage_sizes_modifier+nextrow)); //distribution of modifier lineages weighted by their size
    
       //Neutral Modifier Mutations:

       //number of neutral modifier mutations
        //number_of_mutations.param(std::binomial_distribution<int>::param_type(population_size_non_modifier,Um)); //update binomial distribution parameters:
        number_of_mutations_poisson.param(std::poisson_distribution<int>::param_type(population_size_non_modifier*Um)); //update poisson distribution parameters:
        num_neutral_modifier_mutants =number_of_mutations(generator); //number of new neutral modifier mutations
        //print number of neutral modifier mutations
        //sample backgrounds
        for (int i=0; i<num_neutral_modifier_mutants; i++) {
            background = sample_lineage(generator);
            sizes_modifier[background]++;
        }

        //Beneficial Mutations:
        
        //number and location of new beneficial lineages
        //number_of_mutations.param(std::binomial_distribution<int>::param_type(population_size_non_modifier,U1)); //update binomial distribution parameters:
        number_of_mutations_poisson.param(std::poisson_distribution<int>::param_type(population_size_non_modifier*U1)); //update poisson distribution parameters:
        num_beneficial_mutants = number_of_mutations_poisson(generator); //number of new beneficial mutations

        //sample background and mutation location ensuring no reversion
        for (int i=0; i<num_beneficial_mutants; i++) {
            background = sample_lineage(generator);
            location= L/2;
            reversion=true;
            //while location is L/2 or reversion=true
            while (location == L/2 || reversion==true) {
                //use below to sample from fixed beneficial sites
                location = beneficial_loci[distribution_ben_loc(generator)];
                //use below to randomly sample along genome:
                //location = distribution(generator);
                // search location in polymorphic_sites[background]
                if (std::find(polymorphic_sites[background], polymorphic_sites[background] + MAX_POLY, location) == polymorphic_sites[background] + MAX_POLY) {
                    reversion=false;
                }
            }
            lineage_sizes[nextrow]=1;
            lineage_fitnesses[nextrow]=lineage_fitnesses[background]+s1;

            // Copy polymorphic sites from background lineage to new lineage until the first non-zero element
            std::copy(polymorphic_sites[background], polymorphic_sites[background] + MAX_POLY, polymorphic_sites[nextrow]);
            std::copy(is_site_recombined[background], is_site_recombined[background] + MAX_POLY, is_site_recombined[nextrow]);

            // Set the new mutation location
            polymorphic_sites[nextrow][next_column1[background]] = location;

            // Increment nextrow and next_column1
            next_column1[nextrow]=next_column1[background]+1;
            nextrow++;
        }
        //number and location of new beneficial modifier lineages
        number_of_mutations.param(std::binomial_distribution<int>::param_type(population_size_modifier,U1_m)); 
        num_beneficial_modifier_mutants =number_of_mutations(generator); 

        //sample background and mutation location ensuring no reversion
        for (int i=0; i<num_beneficial_modifier_mutants; i++) {
            background = sample_lineage_modifier(generator);
            location= L/2;
            reversion=true;
            //while location is L/2 or reversion=true
            while (location == L/2 || reversion==true) {
                location = distribution(generator);
                // search location in polymorphic_sites[background]
                if (std::find(polymorphic_sites[background], polymorphic_sites[background] + MAX_POLY, location) == polymorphic_sites[background] + MAX_POLY) {
                    reversion=false;
                }
            }
            lineage_sizes_modifier[nextrow]=1;
            lineage_fitnesses[nextrow]=lineage_fitnesses[background]+s1_m;

            // Copy polymorphic sites from background lineage to new lineage until the first non-zero element
            std::copy(polymorphic_sites[background], polymorphic_sites[background] + MAX_POLY, polymorphic_sites[nextrow]);
            std::copy(is_site_recombined[background], is_site_recombined[background] + MAX_POLY, is_site_recombined[nextrow]);

            // Set the new mutation location
            polymorphic_sites[nextrow][next_column1[background]] = location;

            // Increment nextrow and next_column1
            next_column1[nextrow]=next_column1[background]+1;
            nextrow++;
        }
        //RECOMBINATION IN BACKGROUND LINEAGES
        //update number_of_recombinants parameters
        //number_of_recombinants.param(std::binomial_distribution<int>::param_type(population_size_non_modifier,r)); //update binomial distribution parameters:
        number_of_recombinants_poisson.param(std::poisson_distribution<int>::param_type(population_size_non_modifier*r));
        num_recombinants = number_of_recombinants_poisson(generator); //number of new recombinants

        //update bernoulli distribution parameters
        sample.param(std::bernoulli_distribution::param_type(1.0-static_cast<double>(population_size_non_modifier)/static_cast<double>(population_size_non_modifier+population_size_modifier))); //update bernoulli distribution parameters:
        
        //iterate over recombination events
        for (int z=0; z<num_recombinants; z++) {
            //Determine Donor, Acceptor Genetic Backgrounds

            // the type of recombination determines whether recombinants are acceptors/donors/both
            if (recombination_type==0) {
                non_modifier_is_donor = true;
                modifier_is_donor=false;
            }
            else if (recombination_type==1) {
                non_modifier_is_acceptor = true;
                modifier_is_acceptor=false;
            }
            else if (recombination_type==2) {
                is_non_modifier_acceptor_or_donor = donor_or_acceptor(generator);
                if (is_non_modifier_acceptor_or_donor==0) {
                    non_modifier_is_acceptor = true;
                    modifier_is_acceptor=false;
                }
                else if (is_non_modifier_acceptor_or_donor==1) {
                    non_modifier_is_donor = true;
                    modifier_is_donor=false;
                }
            }
            if (non_modifier_is_donor==true) { // non modifier is donor
                //sample donor
                donor = sample_lineage(generator);
                //sample whether acceptor is modifier or non modifier
                modifier_is_acceptor = sample(generator);
                //if modifier_is_acceptor is 0, non modifier is acceptor
                if (modifier_is_acceptor==false) { //acceptor=non-modifier; donor=non-modifier
                    acceptor = sample_lineage(generator);
                    non_modifier_is_acceptor=true;
                    mismatch=false;
                }
                //else if modifier_is_acceptor is 1 modifier is acceptor
                else if (modifier_is_acceptor==true) { //acceptor=modifier; donor=non-modifier
                    acceptor = sample_lineage_modifier(generator); 
                    non_modifier_is_acceptor=false;
                    mismatch=true;               
                }
            }
            else if (non_modifier_is_acceptor==true) {
                // non modifier is acceptor
                acceptor = sample_lineage(generator);
                //sample whether donor is modifier or non modifier
                modifier_is_donor = sample(generator);
                //if modifier_is_donor is 0, non modifier is donor
                if (modifier_is_donor==false) { //acceptor=non-modifier; donor=non-modifier
                    donor = sample_lineage(generator);
                    non_modifier_is_donor=true;
                    mismatch=false;
                }
                //else if modifier_is_donor is 1 modifier is donor
                else if (modifier_is_donor==true) { //acceptor=non-modifier; donor=modifier
                    donor = sample_lineage_modifier(generator);
                    non_modifier_is_donor=false;
                    mismatch=true;
                }
            }

            if (donor!=acceptor or mismatch==true)   {
                //recombination start and end sites for non modifier population 
                start_location = distribution_r(generator);   
                end_location=start_location+transfer_length;
                //if end location is greater than genome length set to genome length
                if (end_location>L) {
                    end_location=L;
                }
                acceptor_sites = {};
                donor_sites = {};
                acceptor_poly= {}; 
                donor_poly = {};

                //Recombination Process

                //save indices of acceptor/donor sites in transferred region
                for (int j = 0; j < MAX_POLY; j++) {
                    if (polymorphic_sites[acceptor][j]>=start_location && polymorphic_sites[acceptor][j]<=end_location) {
                        acceptor_sites.push_back(j-acceptor_sites.size());
                        acceptor_poly.push_back(polymorphic_sites[acceptor][j]);
                    }
                    if (polymorphic_sites[donor][j]>=start_location && polymorphic_sites[donor][j]<=end_location) {
                        donor_sites.push_back(j);
                        donor_poly.push_back(polymorphic_sites[donor][j]);
                    }
                }
                //create a vector of elements in donor_sites and acceptor_sites that are not in both
                donor_acceptor_diff={};
                std::sort(donor_poly.begin(), donor_poly.end());
                std::sort(acceptor_poly.begin(), acceptor_poly.end());
                std::set_symmetric_difference(acceptor_poly.begin(), acceptor_poly.end(), donor_poly.begin(), donor_poly.end(), std::back_inserter(donor_acceptor_diff));
                
                //if donor_sites is non-empty or acceptor_sites is non-empty
                if ((!donor_acceptor_diff.empty() || (start_location <= L/2 && end_location >= L/2 && mismatch == true))) {
                    //copy genotype of acceptor to new row
                    std::copy(polymorphic_sites[acceptor], polymorphic_sites[acceptor] + MAX_POLY, polymorphic_sites[nextrow]);
                    std::copy(is_site_recombined[acceptor], is_site_recombined[acceptor] + MAX_POLY, is_site_recombined[nextrow]);
                    next_column1[nextrow]=next_column1[acceptor];
                    // Remove sites from the transferred region
                    for (int j : acceptor_sites) {
                        std::copy(polymorphic_sites[nextrow] + j + 1, polymorphic_sites[nextrow] + MAX_POLY, polymorphic_sites[nextrow] + j);
                        std::copy(is_site_recombined[nextrow] + j + 1, is_site_recombined[nextrow] + MAX_POLY, is_site_recombined[nextrow] + j);
                        next_column1[nextrow]--;
                    }

                    //for each value in donor_sites, add site in transferred region
                    for (int j = 0; j < donor_sites.size(); j++) {
                        polymorphic_sites[nextrow][next_column1[nextrow]]=polymorphic_sites[donor][donor_sites[j]];
                        is_site_recombined[nextrow][next_column1[nextrow]]=true;
                        next_column1[nextrow]++;
                    }
                

                    //check if genotype exists--only if use if needed, this is costly
                    permutation=false;
                    //if new genotype does not exist, keep it and update vectors
                    if (permutation==false) {
                        //if modifier loci is transferred
                        if (non_modifier_is_donor==true and modifier_is_acceptor==true) {
                            //Donor=non-modifier; Acceptor=modifier
                            if (start_location <= L/2 && end_location >= L/2) { //new lineage is non-modifier
                                lineage_sizes[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1-acceptor_sites.size()*s1_m);
                            }
                            else { //new lineage is modifier
                                lineage_sizes_modifier[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1-acceptor_sites.size()*s1_m);
                            }
                            lineage_sizes_modifier[acceptor]--;
                        }
                        else if (modifier_is_donor==true and non_modifier_is_acceptor==true) {
                            //Donor=modifier; Acceptor=non-modifier
                            if (start_location <= L/2 && end_location >= L/2) { //new lineage is modifier
                                lineage_sizes_modifier[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1_m-acceptor_sites.size()*s1);
                            }
                            else { //new lineage is non-modifier
                                lineage_sizes[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1_m-acceptor_sites.size()*s1);
                            }
                            lineage_sizes[acceptor]--;
                        }
                        else if (non_modifier_is_donor==true and non_modifier_is_acceptor==true) {
                            //Donor=non-modifier; Acceptor=non-modifier-->new lineage is non-modifier
                            lineage_sizes[nextrow]=1;
                            lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1-acceptor_sites.size()*s1);
                            lineage_sizes[acceptor]--;
                        }
                        else if (modifier_is_donor==true and modifier_is_acceptor==true) {
                            //Donor=modifier; Acceptor=modifier-->new lineage is modifier
                            lineage_sizes_modifier[nextrow]=1;
                            lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1_m-acceptor_sites.size()*s1_m);
                            lineage_sizes_modifier[acceptor]--;
                        }  
                        if (lineage_fitnesses[nextrow]>=max_fitness && lineage_fitnesses[nextrow]>lineage_fitnesses[acceptor]) {
                            number_recomb_events_viable++;
                        }
                        nextrow++;
                    }
                }
            }
        }

        //RECOMBINATION IN MODIFIER LINEAGES
        //number_of_recombinants.param(std::binomial_distribution<int>::param_type(population_size_modifier,r_m)); //update binomial distribution parameters:
        number_of_recombinants_poisson.param(std::poisson_distribution<int>::param_type(population_size_modifier*r_m));
        num_modifier_recombinants =number_of_recombinants_poisson(generator); //number of new recombinants

        //iterate over recombination events
        for (int z=0; z<num_modifier_recombinants; z++) {

            //Determine Donor, Acceptor Genetic Backgrounds

            // the type of recombination determines whether recombinants are acceptors/donors/both
            if (recombination_type==0) {
                modifier_is_donor = true;
                non_modifier_is_donor=false;
            }
            else if (recombination_type==1) {
                modifier_is_acceptor = true;
                non_modifier_is_acceptor=false;
            }
            else if (recombination_type==2) {
                is_non_modifier_acceptor_or_donor = donor_or_acceptor(generator);
                if (is_modifier_acceptor_or_donor==0) {
                    modifier_is_donor = true;
                    non_modifier_is_donor=false;
                }
                else if (is_modifier_acceptor_or_donor==1) {
                    modifier_is_acceptor = true;
                    non_modifier_is_acceptor=false;
                }
            }
            if (modifier_is_donor==true) { // modifier is donor
                //sample donor
                donor = sample_lineage_modifier(generator);
                //sample whether acceptor is modifier or non modifier
                modifier_is_acceptor = sample(generator);
                //if modifier_is_acceptor is 0, non modifier is acceptor
                if (modifier_is_acceptor==false) { //acceptor=non-modifier; donor=modifier
                    acceptor = sample_lineage(generator);
                    non_modifier_is_acceptor=true;
                    mismatch=true;
                }
                //else if modifier_is_acceptor is 1 modifier is acceptor
                else if (modifier_is_acceptor==true) { //acceptor=modifier; donor=modifier
                    acceptor = sample_lineage_modifier(generator);
                    non_modifier_is_acceptor=false;
                    mismatch=false;           
                }
            }
            else if (modifier_is_acceptor==true) {// modifier is acceptor
                acceptor = sample_lineage_modifier(generator);
                //sample whether donor is modifier or non modifier
                modifier_is_donor = sample(generator);
                //if modifier_is_donor is 0, non modifier is donor
                if (modifier_is_donor==false) { //acceptor=modifier; donor=non-modifier
                    donor = sample_lineage(generator);
                    non_modifier_is_donor=true;
                    mismatch=true;
                }
                //else if modifier_is_donor is 1 modifier is donor
                else if (modifier_is_donor==true) { //acceptor=modifier; donor=modifier
                    donor = sample_lineage_modifier(generator);
                    non_modifier_is_donor=false;
                    mismatch=false;
                }
            }

            if (donor!=acceptor || mismatch==true)   {
                //recombination start and end sites for non modifier population 
                start_location = distribution_r(generator);   
                end_location=start_location+transfer_length;
                //if end location is greater than genome length set to genome length
                if (end_location>L) {
                    end_location=L;
                }
                acceptor_sites = {};
                donor_sites = {};
                acceptor_poly= {};
                donor_poly = {};

                //Recombination Process

                //save indices of acceptor/donor sites in transferred region
                for (int j = 0; j < MAX_POLY; j++) {
                    if (polymorphic_sites[acceptor][j]>=start_location && polymorphic_sites[acceptor][j]<=end_location) {
                        acceptor_sites.push_back(j-acceptor_sites.size());
                        acceptor_poly.push_back(polymorphic_sites[acceptor][j]);
                    }
                    if (polymorphic_sites[donor][j]>=start_location && polymorphic_sites[donor][j]<=end_location) {
                        donor_sites.push_back(j);
                        donor_poly.push_back(polymorphic_sites[donor][j]);
                    }
                }

                //create a vector of elements in donor_sites and acceptor_sites that are not in both
                donor_acceptor_diff={};
                std::sort(donor_poly.begin(), donor_poly.end());
                std::sort(acceptor_poly.begin(), acceptor_poly.end());
                std::set_symmetric_difference(acceptor_poly.begin(), acceptor_poly.end(), donor_poly.begin(), donor_poly.end(), std::back_inserter(donor_acceptor_diff));
                //if donor_sites is non-empty or acceptor_sites is non-empty
                if (!donor_acceptor_diff.empty() || (start_location <= L/2 && end_location >= L/2 && mismatch == true)) {
                    //copy genotype of acceptor to new row
                    std::copy(polymorphic_sites[acceptor], polymorphic_sites[acceptor] + MAX_POLY, polymorphic_sites[nextrow]);
                    std::copy(is_site_recombined[acceptor], is_site_recombined[acceptor] + MAX_POLY, is_site_recombined[nextrow]);
                    next_column1[nextrow]=next_column1[acceptor];
                    //for each value in acceptor_sites, delete site in transferred region
                    for (int j : acceptor_sites) {
                        std::copy(polymorphic_sites[nextrow] + j + 1, polymorphic_sites[nextrow] + MAX_POLY, polymorphic_sites[nextrow] + j);
                        std::copy(is_site_recombined[nextrow] + j + 1, is_site_recombined[nextrow] + MAX_POLY, is_site_recombined[nextrow] + j);
                        next_column1[nextrow]--;
                    }
                    //for each value in donor_sites, add site in transferred region
                    for (int j = 0; j < donor_sites.size(); j++) {
                        polymorphic_sites[nextrow][next_column1[nextrow]]=polymorphic_sites[donor][donor_sites[j]];
                        is_site_recombined[nextrow][next_column1[nextrow]]=true;
                        next_column1[nextrow]++;
                    }
                
                    permutation=false;
                    //if new genotype does not exist, keep it and update vectors
                    if (permutation==false) {
                        //check if modifier loci is transferred
                        if (non_modifier_is_donor==true and modifier_is_acceptor==true) {
                            //Donor=non-modifier; Acceptor=modifier
                            if (start_location <= L/2 && end_location >= L/2) { //new lineage is non-modifier
                                lineage_sizes[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1-acceptor_sites.size()*s1_m);
                            }
                            else { //new lineage is modifier
                                lineage_sizes_modifier[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1-acceptor_sites.size()*s1_m);
                            }
                            lineage_sizes_modifier[acceptor]--;
                        }
                        else if (modifier_is_donor==true and non_modifier_is_acceptor==true) {
                            //Donor=modifier; Acceptor=non-modifier
                            if (start_location <= L/2 && end_location >= L/2) { //new lineage is modifier
                                lineage_sizes_modifier[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1_m-acceptor_sites.size()*s1);
                            }
                            else { //new lineage is non-modifier
                                lineage_sizes[nextrow]=1;
                                lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1_m-acceptor_sites.size()*s1);
                            }
                            lineage_sizes[acceptor]--;
                        }
                        else if (non_modifier_is_donor==true and non_modifier_is_acceptor==true) {
                            //Donor=non-modifier; Acceptor=non-modifier-->new lineage is non-modifier
                            lineage_sizes[nextrow]=1;
                            lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1-acceptor_sites.size()*s1);
                            lineage_sizes[acceptor]--;
                        }
                        else if (modifier_is_donor==true and modifier_is_acceptor==true) {
                            //Donor=modifier; Acceptor=modifier-->new lineage is modifier
                            lineage_sizes_modifier[nextrow]=1;
                            lineage_fitnesses[nextrow]=lineage_fitnesses[acceptor]+(donor_sites.size()*s1_m-acceptor_sites.size()*s1_m);
                            lineage_sizes_modifier[acceptor]--;
                        }  
                        nextrow++;
                    }
                    //print polymorphic_sites[acceptor], polymorphic_sites[donor], polymorphic_sites[nextrow-1], start_location
                }
            }
        }
        // UPDATE VECTORS WITH EXPONENTIAL GROWTH
        for (int i=0; i<nextrow_old; i++) {
            lineage_sizes[i]=sizes[i];
            lineage_sizes_modifier[i]=sizes_modifier[i];
        }
            
        // DELETE LINEAGES THAT ARE ZEROS
        for (int i=0; i<nextrow;) {
            if (lineage_sizes[i] == 0 and lineage_sizes_modifier[i] == 0) {
                // overwrite the current lineage with the last lineage
                lineage_sizes[i] = lineage_sizes[nextrow - 1];
                lineage_sizes_modifier[i] = lineage_sizes_modifier[nextrow - 1];
                lineage_fitnesses[i] = lineage_fitnesses[nextrow - 1];
                next_column1[i]=next_column1[nextrow-1];
                std::copy(polymorphic_sites[nextrow - 1], polymorphic_sites[nextrow - 1] + MAX_POLY, polymorphic_sites[i]);
                std::copy(is_site_recombined[nextrow - 1], is_site_recombined[nextrow - 1] + MAX_POLY, is_site_recombined[i]);
                
                lineage_sizes[nextrow - 1] = 0;
                lineage_sizes_modifier[nextrow - 1] = 0;
                lineage_fitnesses[nextrow - 1] = 0;
                next_column1[nextrow-1]=0;
                std::fill_n(polymorphic_sites[nextrow - 1], MAX_POLY, 0);
                std::fill_n(is_site_recombined[nextrow - 1], MAX_POLY, false);
                // Decrement the count of lineages
                nextrow--;
            }
            else {
                i++;
            }
        }
        //DELETE POLYMORPHISMS THAT HAVE FIXED
        if (t%50==0) {
            for (int i = 0; i < MAX_POLY;) {
                in_all_rows = false;
                if (polymorphic_sites[0][i] != 0) {
                    in_all_rows = true;
                }
                int j=1;
                while (in_all_rows==true && j<nextrow) {
                        auto it = std::find(polymorphic_sites[j], polymorphic_sites[j] + MAX_POLY, polymorphic_sites[0][i]);
                        int index_to_specific_fixed_site = std::distance(polymorphic_sites[j], it);
                        if (it == polymorphic_sites[j] + MAX_POLY || is_site_recombined[j][index_to_specific_fixed_site]!=is_site_recombined[0][i]) {
                            in_all_rows = false;
                    }
                    j++;
                }
                if (in_all_rows == true) {
                    polymorphism_to_remove=polymorphic_sites[0][i];
                    is_removed_site_recombined=is_site_recombined[0][i];
                    total_fixations++;
                    //polymorphic_sites_population.erase(polymorphism_to_remove);
                    fixed_polymorphisms.push_back(polymorphism_to_remove);
                    if (is_removed_site_recombined==true) {
                        recombined_fixations++;
                    }
                    for (int m = 0; m < nextrow; m++) {
                        for (int k = 0; k < MAX_POLY; k++) {
                            if (polymorphic_sites[m][k] == polymorphism_to_remove) {
                                std::copy(polymorphic_sites[m] + k + 1, polymorphic_sites[m] + MAX_POLY, polymorphic_sites[m] + k);
                                std::copy(is_site_recombined[m] + k + 1, is_site_recombined[m] + MAX_POLY, is_site_recombined[m] + k);
                                break;
                            }
                        }
                        next_column1[m]--;
                    }
                    // Find the index of polymorphism_to_remove in beneficial_loci and replace it with a new locus that is not in beneficial_loci
                    // Sample beneficial loci but do not allow L/2
                    bool new_locus = false;
                    int new_locus_value = L/2;
                    auto it= std::find(beneficial_loci, beneficial_loci + num_beneficial_loci, polymorphism_to_remove);
                    int index_of_fixed_poly=std::distance(beneficial_loci, it);
                    while (!new_locus) {
                        // Generate a new locus
                        new_locus_value = distribution(generator);

                        // Ensure it's not L/2 and not already chosen
                        if (new_locus_value != L / 2 && 
                            std::find(beneficial_loci, beneficial_loci + num_beneficial_loci, new_locus_value) == beneficial_loci + num_beneficial_loci) {
                            beneficial_loci[index_of_fixed_poly] = new_locus_value;
                            new_locus = true;
                        }
                    }
                }
                else {
                    i++;
                }
            }
        }

        //calculate mean fitness of whole population
        mean_fitness = 0;
        for (int i = 0; i < nextrow; i++) {
            mean_fitness += lineage_fitnesses[i] * (lineage_sizes[i]+lineage_sizes_modifier[i]);
        }
        //population_size_non_modifier is sum of lineage_sizes
        population_size_non_modifier=std::accumulate(lineage_sizes, lineage_sizes+nextrow, 0.0); //population size of non-modifier lineages
        population_size_modifier=std::accumulate(lineage_sizes_modifier, lineage_sizes_modifier+ nextrow, 0.0); //population size of modifier lineages
        mean_fitness = mean_fitness / (population_size_non_modifier+population_size_modifier);
        X_final+=mean_fitness;
        //subtract mean fitness from all lineage fitnesses
        for (int i = 0; i < nextrow; i++) {
            lineage_fitnesses[i] = lineage_fitnesses[i] - mean_fitness;
        }

        //if lineage sizes is empty break loop
        if (population_size_non_modifier==0) {
            tfix=t-teq;
            break;
        }
        //if t mod 1000 print t
        if (t%2==0) {
            std::cout << t << std::endl;
            std::cout << nextrow << std::endl;
        }
        //if timer shows more than 47.5 hours have passed
        if (std::chrono::duration_cast<std::chrono::minutes>(std::chrono::steady_clock::now() - start_time).count() > 2850) {
            double v = X_final/static_cast<double>(tmax);
            double fraction_recombined=static_cast<double>(recombined_fixations)/static_cast<double>(total_fixations);
            std::cout << "fraction_recombined: " << fraction_recombined << "\n";
            std::cout << "v: " << v << "\n";
            std::cout << "total_fixations: " << total_fixations << "\n";
            std::stringstream filename;
            filename << "simulation_outputs_final_"
                    << "N" << std::fixed << std::setprecision(2) << log10(N) << "_"
                    << "Ub" << log10(U1) << "_"
                    << "sb" << log10(s1) << "_"
                    << "transfer_length" << log10(transfer_length) << "_"
                    << "L" << log10(L) << "_"
                    << "R" << log10(r) << "_"
                    << "nbl" << log10(num_beneficial_loci) 
                    << ".txt";

            std::ofstream myfile(filename.str(), std::ios_base::app);
            // Write simulation parameters and outputs to file
            myfile << "PARAMETERS: " << std::endl;
            myfile << "random seed: \t" << seed << std::endl;
            myfile << "N: \t" << N << std::endl;
            myfile << "Ub: \t" << U1 << std::endl;
            myfile << "sb: \t" << s1 << std::endl;
            myfile << "Ud: \t" << U2 << std::endl;
            myfile << "rL: \t" << r << std::endl;
            myfile << "rl: \t" << r * static_cast<double>(transfer_length) / static_cast<double>(L) << std::endl;
            myfile << "L: \t" << L << std::endl;
            myfile << "total_time: " << t << std::endl;
            myfile << "t_eq: " << teq << std::endl;
            myfile << "number_beneficial_loci: " << num_beneficial_loci << std::endl;
            myfile << "l: \t" << transfer_length << std::endl;

            myfile << "OUTPUTS " << std::endl;
            myfile << "v: \t" << v << std::endl;
            myfile << "total_fixations: \t" << total_fixations << std::endl;
            myfile << "fraction recombined: \t" << fraction_recombined << std::endl;

            // Print fixed polymorphisms
            myfile << "fixed polymorphisms: " << std::endl;
            for (const auto& polymorphism : fixed_polymorphisms) {
                myfile << polymorphism << std::endl;
            }

            myfile.close();
            //end code entirely
            exit(0);
        }
        if (t % 10000 == 0 && t > 0) {
            double v = X_final / static_cast<double>(tmax);
            double fraction_recombined = static_cast<double>(recombined_fixations) / static_cast<double>(total_fixations);

            std::cout << "fraction_recombined: " << fraction_recombined << "\n";
            std::cout << "v: " << v << "\n";
            std::cout << "total_fixations: " << total_fixations << "\n";

            // Generate the filename with an index based on the generation
            std::stringstream filename;
            filename << "simulation_outputs_"
                    << "N" << std::fixed << std::setprecision(2) << log10(N) << "_"
                    << "Ub" << log10(U1) << "_"
                    << "sb" << log10(s1) << "_"
                    << "transfer_length" << log10(transfer_length) << "_"
                    << "L" << log10(L) << "_"
                    << "R" << log10(r) << "_"
                    << "nbl" << log10(num_beneficial_loci) 
                    << "_gen" << t  // Add an index based on the generation t
                    << ".txt";

            std::ofstream myfile(filename.str(), std::ios_base::app);
            if (myfile.is_open()) {
                myfile << "fraction_recombined: " << fraction_recombined << "\n";
                myfile << "v: " << v << "\n";
                myfile << "total_fixations: " << total_fixations << "\n";
                // Add other data to the file as needed
            }
            myfile.close();
        }
    }
    
    
    double v = X_final/static_cast<double>(tmax);
    double fraction_recombined=static_cast<double>(recombined_fixations)/static_cast<double>(total_fixations);
    std::cout << "fraction_recombined: " << fraction_recombined << "\n";
    std::cout << "v: " << v << "\n";
    std::cout << "total_fixations: " << total_fixations << "\n";
    std::stringstream filename;
    filename << "simulation_outputs_"
             << "N" << std::fixed << std::setprecision(2) << log10(N) << "_"
             << "Ub" << log10(U1) << "_"
             << "sb" << log10(s1) << "_"
             << "transfer_length" << log10(transfer_length) << "_"
             << "L" << log10(L) << "_"
             << "R" << log10(r) << "_"
             << "nbl" << log10(num_beneficial_loci) 
             << ".txt";

    std::ofstream myfile(filename.str(), std::ios_base::app);

    // Write simulation parameters and outputs to file
    myfile << "PARAMETERS: " << std::endl;
    myfile << "random seed: \t" << seed << std::endl;
    myfile << "N: \t" << N << std::endl;
    myfile << "Ub: \t" << U1 << std::endl;
    myfile << "sb: \t" << s1 << std::endl;
    myfile << "Ud: \t" << U2 << std::endl;
    myfile << "rL: \t" << r << std::endl;
    myfile << "rl: \t" << r * static_cast<double>(transfer_length) / static_cast<double>(L) << std::endl;
    myfile << "L: \t" << L << std::endl;
    myfile << "total_time: " << tmax+teq << std::endl;
    myfile << "t_eq: " << teq << std::endl;
    myfile << "number_beneficial_loci: " << num_beneficial_loci << std::endl;
    myfile << "l: \t" << transfer_length << std::endl;

    myfile << "OUTPUTS " << std::endl;
    myfile << "v: \t" << v << std::endl;
    myfile << "total_fixations: \t" << total_fixations << std::endl;
    myfile << "fraction recombined: \t" << fraction_recombined << std::endl;

    // Print fixed polymorphisms
    myfile << "fixed polymorphisms: " << std::endl;
    for (const auto& polymorphism : fixed_polymorphisms) {
        myfile << polymorphism << std::endl;
    }

    myfile.close();



    // Free the dynamically allocated memory
    delete[] lineage_sizes;
    delete[] lineage_sizes_modifier;
    delete[] expected_lineage_sizes;
    delete[] expected_lineage_sizes_modifier;
    delete[] lineage_fitnesses;
    delete[] polymorphic_sites;
    delete[] is_site_recombined;
    delete[] sizes;
    delete[] sizes_modifier;
    delete[] next_column1;

    return tfix;
}


int main(int argc, char* argv[]) {

    // Read in the command-line parameters
    double N = std::atof(argv[1]);             // Population size
    int transfer_length = std::atoi(argv[2]);             // Transfer length (lowercase l)
    int L = std::atoi(argv[3]);                // Genome length
    double s1 = std::atof(argv[4]);            // Selection coefficient for beneficial mutations
    double R = std::atof(argv[5]);             // Recombination rate
    double U1 = std::atof(argv[6]);            // Mutation rate for beneficial mutations
    int number_beneficial_loci = std::atoi(argv[7]);      // Number of beneficial loci

    //SET PARAMETERS

    //----------------------------------------------------------------------------------------------------------------------------------------------------
    //const double N=100000000000; //population size
    //const int L=1000000; //genome length

    //const double s1=0.05; //selection coefficient for beneficial muttions
    const double s2=0; //selection coefficient for deleterious mutations
    //const double U1=.0000001; //mutation rate for beneficial mutations
    const double U2=0; //mutation rate for deleterious mutations

    const double s1_m=0; //selection coefficient for modifier beneficial muttions
    const double s2_m=0; //selection coefficient for modifier deleterious mutations
    const double U1_m=0.000000; //mutation rate for modifier beneficial mutations
    const double U2_m=0; //mutation rate for modifier deleterious mutations

    //const int number_beneficial_loci=10000; //number of beneficial loci
    //const double R.0001; //recombination rate
    const double r_m=0.000; //recombination rate for modifier
    //const int transfer_length =316; //length of transferred region
    int recombination_type=0; //if 0, modifier more likely to be donor, if 1 modifier more likely to be acceptor, if 2 equal increase in probability of being donor or acceptor 
    double mu=0.000000; //rate of modifiers being introduced

    //------------------------------------------------------------------------------------------------------------------------------------------------------
    int tfix = evolve(mu, N, L, s1, s2, U1, U2, U1_m, U2_m, s1_m, s2_m, R, r_m, transfer_length, recombination_type, number_beneficial_loci);

    //open a textfile
    return 0;
}



