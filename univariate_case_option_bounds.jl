using MosekTools
using MomentOpt
using DynamicPolynomials
using Printf

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


k = 105     #strike of option we want to bound
strikes = [95, 100, 110, 115, 120]      #observable strike
prices = [12.875, 8.375, 1.875, 0.625, 0.25]    #obserable prices

##
function boundsOnPrice(strikes, prices, k, M, silent)

    relaxation_order = 1    #level of relaxation you want to compute, always tight for level 1

    @polyvar x      #initialize variable

    #this function generates the necessary semialgebraic sets
    function generateSemiAlgSets(strikes, k, x)
        knew = [0.0]
        for el in strikes
            push!(knew, el)
        end
        #push!(knew, 1.0)
        setList = []
        for i = 1:length(knew)-1
            set = @set((x - knew[i]) * (knew[i+1] - x) >= 0)
            push!(setList, set)
        end
        push!(setList, @set(x - knew[end] >= 0))
        #ind = findall(i -> i == k, strikes)
        return setList#, strikes, ind[1]
    end

    #this function normalized the data
    function scaleInput(strikes, prices, k)
        #for now I just set B to be large enough
        #B = prices[end-1]/(prices[end-1]-prices[end])*strikes[end]-prices[end]/(prices[end-1]-prices[end])*strikes[end-1]

        strikes2 = deepcopy(strikes)
        push!(strikes2, k)
        sort!(strikes2)
        ind = findall(i -> i == k, strikes2)
        return strikes2, prices, ind[1]
    end

    strikes2, prices2, ind = scaleInput(strikes, prices, k)

    setList = generateSemiAlgSets(strikes2, k, x)

    gmp = GMPModel(optimizer_with_attributes(Mosek.Optimizer))

    if silent
        set_optimizer_attribute(gmp, MOI.Silent(), true)
    end

    #initialize measures
    μ = @variable gmp [i = 1:length(setList)] Meas([x]; support = setList[i])

    #add constraints
    for i = 1:ind-1
        @constraint gmp sum(
            Mom(x - strikes2[i], μ[j]) for j = i+1:length(setList)
        ) == prices2[i]
    end

    for i = ind+1:length(strikes2)
        @constraint gmp sum(
            Mom(x - strikes2[i], μ[j]) for j = i+1:length(setList)
        ) == prices2[i-1]
    end

    @constraint gmp sum(Mom(x^2, μ[j]) for j = 1:length(setList)) <= M

    @constraint gmp sum(Mom(1, μ[j]) for j = 1:length(setList)) == 1


    obj = sum(Mom(x - strikes2[ind], μ[i]) for i = ind+1:length(setList))

    #get lower bound
    set_approximation_degree(gmp, 2 * relaxation_order)
    @objective(gmp, Min, obj)
    optimize!(gmp)
    sol1 = []
    for i = 1:length(μ)
        push!(sol1, measure(μ[i]))
    end

    if !silent
        display(termination_status(gmp))
        display(dual_status(gmp))
        display(primal_status(gmp))
    end

    lower = objective_value(gmp)

    #get upper bound
    @objective(gmp, Max, obj)
    optimize!(gmp)
    upper = objective_value(gmp)

    strike = k
    print("\n")

    @printf "The price of an option on this asset with strike price %d should lie in [%.3f,%.3f]" strike lower upper

    sol2 = []
    for i = 1:length(μ)
        push!(sol2, measure(μ[i]))
    end
    return sol1, sol2

end


sol1, sol2 = boundsOnPrice(strikes, prices, k, 20000, true)


##

#for comparison one can check the bound from Bertsimas and Popsecu
function BertsPopBound(x)

    k = [95, 100, 110, 115, 120]
    a = [12.875, 8.375, 1.875, 0.625, 0.25]

    j = findfirst(i -> i > x, k) - 1

    qm1 =
        a[j] * (x - k[j-1]) / (k[j] - k[j-1]) +
        a[j-1] * (k[j] - x) / (k[j] - k[j-1])
    qm2 =
        a[j+1] * (k[j+2] - x) / (k[j+2] - k[j+1]) +
        a[j+2] * (x - k[j+1]) / (k[j+2] - k[j+1])
    qp =
        a[j] * (k[j+1] - x) / (k[j+1] - k[j]) +
        a[j+1] * (x - k[j]) / (k[j+1] - k[j])
    lower = maximum([qm1, qm2])
    upper = qp

    display((lower, upper))
end

BertsPopBound(k)
