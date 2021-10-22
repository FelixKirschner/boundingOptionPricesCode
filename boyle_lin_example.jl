using DynamicPolynomials
using MosekTools
using MomentOpt

#Bounds on contingent claims based on several assets Boyle Lin

#=

To use the package MomentOpt you might have to downgrade some other packages.
I used
            JuMP v0.21.4
            MomentOpt v0.2.0
            SumOfSquares v0.4.5

To downgrade packages go into the package manager by pressing "]" in the REPL
then either remove the above packages by entering "rm package_name"
and add the package with specified version by
entering "add package_name @vX.X.X" where X.X.X is the specific version you want
Or you enter
Pkg.add(Pkg.PackageSpec(;name="package_name", version="X.X.X")) in the REPL

=#

##

relaxation_order = 1    #level of relaxation you want to compute
n = 3                   #number of assets
silent = false          #enable or disable solver output

scaling = 200                             #scaling important for numerical stability
mean = [44.21, 44.21, 44.21] / scaling        #given means, normalized


covariance =
      [
            184.04 164.88 164.88               #given coraviance matrix
            164.88 184.04 164.88
            164.88 164.88 184.04
      ] / scaling^2

K = 50 / scaling          #strike price K ∈ { 30, 35, 40, 45, 50 }

@polyvar x[1:n]         #initialize variable

#split domain into polytopes
S1 = @set(
      (x[1] * (K - x[1])) >= 0 &&
      x[2] * (K - x[2]) >= 0 &&
      x[3] * (K - x[3]) >= 0
)
S2 = @set(
      x[1] - K >= 0 &&
      x[2] - K >= 0 &&
      x[3] - K >= 0 &&
      x[1] >= x[2] &&
      x[1] >= x[3]
)
S3 = @set(
      x[1] - K >= 0 &&
      x[2] - K >= 0 &&
      x[3] - K >= 0 &&
      x[2] >= x[1] &&
      x[2] >= x[3]
)
S4 = @set(
      x[1] - K >= 0 &&
      x[2] - K >= 0 &&
      x[3] - K >= 0 &&
      x[3] >= x[1] &&
      x[3] >= x[2]
)

subSets = [S1, S2, S3, S4]

gmp = GMPModel(optimizer_with_attributes(Mosek.Optimizer))
#set_approximation_mode(gmp, PRIMAL_RELAXATION_MODE())
#set_approximation_mode(gmp, DUAL_STRENGTHEN_MODE())
if silent == true
      set_optimizer_attribute(gmp, MOI.Silent(), true)
end

μ = @variable gmp [i = 1:length(subSets)] Meas(
      [x[i] for i = 1:n];
      support = subSets[i],
) #initialize measure defined on semialgebraic sets S_i

#add constraints
for i = 1:n
      @constraint gmp sum(Mom(x[i], μ[j]) for j = 1:length(μ)) == mean[i]
end

for i = 1:n
      for j = i:n
            @constraint gmp sum(
                  Mom((x[i] - mean[i]) * (x[j] - mean[j]), μ[l]) for
                  l = 1:length(μ)
            ) == covariance[i, j]
      end
end

#μ must be a probability measure
@constraint gmp sum(Mom(1, μ[i]) for i = 1:length(μ)) == 1

#objective functions
obj =
      scaling *
      (Mom(x[1] - K, μ[2]) + Mom(x[2] - K, μ[3]) + Mom(x[3] - K, μ[4]))

set_approximation_degree(gmp, 2 * relaxation_order)
@objective gmp Max obj        #for upper bound
#@objective gmp Min obj       #for lower bound

optimize!(gmp)

println(
      " Result Status Codes: ",
      termination_status(gmp),
      " ",
      dual_status(gmp),
      " ",
      primal_status(gmp)
)

println(
      " Objective value: ",
      objective_value(gmp)
)
