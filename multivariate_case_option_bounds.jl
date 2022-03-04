using Combinatorics
using JuMP
using MosekTools
using LinearAlgebra

function compBounds(K, B, M, level, silent, strikes, prices, w)

    #define payoff function of basket option to be determined
    function payoff(x)
        return max(0, sum(w[i] * x[i] for i = 1:length(w)) - K)
    end

    n = size(strikes)[1] #number of assets

    num = size(strikes)[2] #number of strikes

    #auxiliary matrix
    upStrikes = zeros(Float32, n, size(strikes)[2] + 2)

    for i = 1:n
        for j = 1:size(strikes)[2]
            upStrikes[i, j+1] = strikes[i, j]
        end
        upStrikes[i, end] = B
    end

    ##


    #this function returns the tiles of [0,B]^n without considering the objective function
    function getSquares(upStrikes)
        squares = []

        for iter in Iterators.product(
            [
                range(1, size(upStrikes)[2] - 1, length = size(upStrikes)[2] - 1)
                for i = 1:n
            ]...,
        )
            p1 = [upStrikes[i, Int(iter[i])] for i = 1:n]
            p2 = [upStrikes[i, Int(iter[i])+1] for i = 1:n]
            push!(squares, (p1, p2))

        end

        return squares
    end

    sq = getSquares(upStrikes)

    function getNumSquares(sq)
        cnt = 0
        indSplit = []
        for i = 1:length(sq)
            if payoff(sq[i][1]) == 0 && payoff(sq[i][2]) > 0
                cnt += 1
                push!(indSplit, i)
            end
        end
        return cnt, indSplit
    end

    splits = getNumSquares(sq)
    numSets = (size(strikes)[2] + 1)^n + splits[1]

    @info("Domain is partitioned into $numSets sets.")

    identifier = []

    for i = 1:length(sq)
        if in(i, splits[2])
            push!(identifier, (sq[i], 1))
            push!(identifier, (sq[i], 2))
        else
            push!(identifier, (sq[i], 0))
        end
    end
    #display(identifier)
    #used for constructing constraints: "get all indices where this function (max(0, x_i-k_{i,j})) != 0, i.e., "Get relevant sets"
    function getRelSet(asset, str, identifier)
        relSet = []
        strike = strikes[asset, str]
        for i = 1:length(identifier)
            if identifier[i][1][1][asset] >= strike
                push!(relSet, i)
            end
        end
        return unique(relSet)
    end

    #sets at which objective funtion is positive
    function getObjSets(identifier)
        relSet = []
        for i = 1:length(identifier)
            if identifier[i][2] == 2
                push!(relSet, i)
            elseif identifier[i][2] == 0 && payoff(identifier[i][1][1]) > 0#eps #not split and lower left greater zero
                push!(relSet, i)
            end
        end
        return relSet

    end

    ##

    numEqConstr = 0
    numIneqConstr = 0
    numLMI = 0

    degmax = 2

    d = 2 * level + degmax

    #function to generate monomial in n variables up to degree r
    function fillmonomials(n, r)
        monlist = []
        for p in Combinatorics.combinations(1:(n+r), r)
            sort!(p)
            c = zeros(Int64, 1, n + 1)
            pos = 1
            lastPos = 0
            for i in p
                pos = pos + (i - lastPos - 1)
                c[pos] += 1
                lastPos = i
            end
            push!(monlist, c[1:n])
        end
        return monlist
    end

    monomials = fillmonomials(n, d)
    refMons = fillmonomials(n, level)
    ind = Dict(monomials[i] => i for i = 1:length(monomials))

    @info("We introduce $(length(monomials)) variables for each measure.")


    m = Model(Mosek.Optimizer)

    MOI.set(m, MOI.Silent(), silent)

    #each row of this matrix corresponds to the moments up to degree d of a measure
    @variable(m, Y[1:numSets, 1:length(monomials)], base_name = "Y")

    auxList = []

    function e(i)
        ei = [0 for j = 1:n]
        ei[i] = 1
        return ei
    end


    for i = 1:n #add constraints for observable options
        for j = 1:num
            set = getRelSet(i, j, identifier)
            xind = ind[e(i)]
            expr = AffExpr()
            for el in set
                add_to_expression!(expr, Y[el, xind] - (strikes[i, j] * Y[el, end]) / B)
            end
            @constraint(m, expr == prices[i, j] / B)
            numEqConstr += 1
        end
    end

    @constraint(m, sum(Y[i, end] for i = 1:size(Y)[1]) == 1) #probability measure
    numEqConstr += 1
    @constraint(
        m,
        sum(sum(Y[i, ind[2*e(j)]] for j = 1:n) for i = 1:size(Y)[1]) <= M / (B * B)
    ) #finite second moments
    numIneqConstr += 1


    for i = 1:length(identifier) #psd condition, localizing matrices
        push!(
            auxList,
            Array{AffExpr,2}(undef, length(refMons), length(refMons)),
        )
        for j = 1:length(refMons)
            for k = 1:length(refMons)
                auxList[length(auxList)][j, k] =
                    Y[i, ind[refMons[j]+refMons[k]]]
            end
        end
        @constraint(m, auxList[length(auxList)] in PSDCone()) #every measure must have psd moment matrix
        numLMI += 1
        #@constraint(m, auxList[length(auxList)] .>= 0) #every measure must have psd moment matrix

        xvec = []

        for counter = 1:n
            push!(xvec, [
                identifier[i][1][1][counter] / B,
                identifier[i][1][2][counter] / B,
            ]
            )
        end

        for counter = 1:n #for every tile (x_i-a)(b-x_i) succeq 0
            push!(
                auxList,
                Array{AffExpr,2}(undef, length(refMons), length(refMons)),
            )

            for j = 1:length(refMons)
                for k = 1:length(refMons)
                    auxList[length(auxList)][j, k] =
                        -xvec[counter][1] * (Y[i, ind[refMons[j]+refMons[k]]]) +
                        (Y[i, ind[e(counter)+refMons[j]+refMons[k]]])
                    #xvec[counter][3] * (Y[i, ind[2*e(counter)+refMons[j]+refMons[k]]])
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())
            numLMI += 1


            push!(
                auxList,
                Array{AffExpr,2}(undef, length(refMons), length(refMons)),
            )

            for j = 1:length(refMons)
                for k = 1:length(refMons)
                    auxList[length(auxList)][j, k] =
                        xvec[counter][2] * (Y[i, ind[refMons[j]+refMons[k]]]) -
                        (Y[i, ind[e(counter)+refMons[j]+refMons[k]]])
                    #xvec[counter][3] * (Y[i, ind[2*e(counter)+refMons[j]+refMons[k]]])
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())
            numLMI += 1



        end


        if identifier[i][2] == 0 # if tile is not split (x-a)(b-x)
            continue


        elseif identifier[i][2] == 1 #if split and lower (x-a)(b-x) and x+y-K <= 0



            push!(
                auxList,
                Array{AffExpr,2}(undef, length(refMons), length(refMons)),
            )
            for j = 1:length(refMons)
                for k = 1:length(refMons)
                    auxList[length(auxList)][j, k] =
                        K / B * (Y[i, ind[refMons[j]+refMons[k]]]) - sum(w[counter2] * (Y[i, ind[e(counter2)+refMons[j]+refMons[k]]]) for counter2 = 1:n)
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())
            numLMI += 1


        elseif identifier[i][2] == 2 #if split and upper (x-a)(b-x) and x+y-K >= 0


            push!(
                auxList,
                Array{AffExpr,2}(undef, length(refMons), length(refMons)),
            )
            for j = 1:length(refMons)
                for k = 1:length(refMons)
                    auxList[length(auxList)][j, k] =
                        -(K / B) * (Y[i, ind[refMons[j]+refMons[k]]]) + sum(w[counter2] * (Y[i, ind[e(counter2)+refMons[j]+refMons[k]]]) for counter2 = 1:n)
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())
            numLMI += 1

        end

    end


    @constraint(m, Y .>= 0) #we know we are in DNN
    numIneqConstr += size(Y)[1] * size(Y)[2]

    objSets = getObjSets(identifier)
    #display(objSets)
    obj = B * sum(
        sum(w[j] * Y[i, ind[e(j)]] for j = 1:n) -
        K / B * Y[i, ind[[0 for count = 1:n]]] for i in objSets
    )
    @info("LMI: $(numLMI) \n Equality constraints: $(numEqConstr) \n Inequality constraints: $(numIneqConstr) \n")

    #get upper bound
    @objective(m, Max, obj)
    optimize!(m)
    display(termination_status(m))
    #display(dual_status(m))
    #display(primal_status(m))
    print("\n \n")
    upp = value.(obj)
    #print("Upper bound: ", value.(obj), "\n \n")


    #get lower bound
    @objective(m, Min, obj)
    optimize!(m)
    display(termination_status(m))
    #display(dual_status(m))
    #display(primal_status(m))
    #print("\n \n")
    low = value.(obj)
    #print("Lower Bound: ", value.(obj), "\n \n")

    display((upp, low))

    return (upp, low)

end

function checkConsistency(strikes, prices)

    boo = true
    n = size(strikes, 1)

    for i = 1:n

        k = strikes[i, :]
        a = prices[i, :]

        for j = 1:length(k)-1
            if a[j] + k[j] >= a[j+1] + k[j+1]
                boo = false
                println("Not consistent, case 1. -> ( $i, $j )")
            end
            if j > 1
                tmp1 = (a[j-1] - a[j]) / (k[j] - k[j-1])
                tmp2 = (a[j] - a[j+1]) / (k[j+1] - k[j])
                if tmp1 <= tmp2
                    boo = false
                    println("Not consistent, case 2. -> ( $i, $j )")
                end
            end
        end
    end
    println("\n")
    return boo
end


##
#Example strikes and prices
##

strikes = [100 110
    102 107]

prices = [12 3
    10 6]

weights = [1 / 2 1 / 2]

checkConsistency(strikes, prices)

##

#AAPL
strikes = [120 130 145 160 170]
prices = [45.2 35.7 21.75 9.1 3.35]
weights = [1]
checkConsistency(strikes, prices)

#FB
strikes = [155 170 180 190 200 210]
prices = [52.7 38.5 29.85 22 14.75 9.15]
weights = [1]
checkConsistency(strikes, prices)

#NVDA
strikes = [175 180 190 195 227.5]
prices = [57.9 53.2 43.85 39.35 10.75]
weights = [1]
checkConsistency(strikes, prices)


#QCOM
strikes = [130 145 157.2 167.5 175]
prices = [35.35 20.5 8.8 2.32 0.47]
weights = [1]
checkConsistency(strikes, prices)

##
#AAPL, FB, NVDA, QCOM
strikes = [120 130 145 160 170
    155 170 180 190 200
    175 180 190 195 227.5
    130 145 157.5 167.5 175]

prices = [45.2 35.7 21.75 9.1 3.35
    52.7 38.5 29.85 22 14.75
    57.9 53.2 43.85 39.35 10.75
    35.35 20.5 8.8 2.32 0.47]

weights = [1 / 4 1 / 4 1 / 4 1 / 4]
checkConsistency(strikes, prices)

## Artificial example

strikes = [95 100 110 115
    96 102 107 112]
prices = [15.5 11 3 1.5
    14.5 9 6 4]
weights = [1 / 2 1 / 2]
checkConsistency(strikes, prices)

## Artificial example

strikes = [90 95 100 110 120
    90 96 102 107 115]
prices = [20 15.5 12 5.5 1
    20.5 15 10 6 0.75]
weights = [1 / 2 1 / 2]
checkConsistency(strikes, prices)

## Currency basket option

strikes = [135.5 138.5 #GBP/USD
    116 119] #EUR/USD
prices = [2.77 1.17
    2.21 0.67]
weights = [2 / 3 1 / 3]
checkConsistency(strikes, prices)

## Example Bertsimas Popescu

strikes = [95 100 110 115 120]
prices = [12.875 8.375 1.875 0.625 0.25]
weights = [1]
checkConsistency(strikes, prices)

##

compBounds(106, 400, 200000, 1, false, strikes, prices, weights);
println("\n \n \n ")
