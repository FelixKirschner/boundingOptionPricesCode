using Combinatorics
using JuMP
using MosekTools
using ProgressMeter
using LinearAlgebra



function compBounds(K,level, silent, strikes, prices,w)


    B = 400 #We consider the set [0,B]^n
    M = 200
    K = K / B




    #normalize strikes and prices
    strikes = 1 / B * strikes

    prices = 1 / B * prices


    function payoff(x)
        return max(0, sum(w[i] * x[i] for i = 1:length(w)) - K )
    end



    n = size(strikes)[1] #number of assets

    num = size(strikes)[2] #number of strikes

    #auxiliary matrix for normalization
    upStrikes = zeros(Float32, n, size(strikes)[2] + 2)

    for i = 1:n
        for j = 1:size(strikes)[2]
            upStrikes[i, j+1] = strikes[i, j]
        end
        upStrikes[i, end] = 1
    end

    ##


    #this function return the tiles of [0,B]^n without considering the objective function
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

    identifier = []

    for i = 1:length(sq)
        if in(i, splits[2])
            push!(identifier, (sq[i], 1))
            push!(identifier, (sq[i], 2))
        else
            push!(identifier, (sq[i], 0))
        end
    end

    #used for constructing constraints: "get all indices where this function (max(0, x_i-k_{i,j})) != 0, i.e., "Get relevant sets"
    function getRelSet(asset, str, identifier)
        eps = 0.0001
        relSet = []
        strike = strikes[asset, str]
        for i = 1:length(identifier)
            if identifier[i][1][1][asset] >= strike - eps
                push!(relSet, i)
            end
        end
        return relSet
    end

    #sets at which objective funtion is positive
    function getObjSets(identifier)
        relSet = []
        for i = 1:length(identifier)
            if identifier[i][2] == 2
                push!(relSet, i)
            elseif identifier[i][2] == 0 && payoff(identifier[i][1][1]) > 0 #not split and lower left greater zero
                push!(relSet, i)
            end
        end
        return relSet

    end

    ##



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



    m = Model(Mosek.Optimizer)

    MOI.set(m, MOI.Silent(), silent)

    #each row of this matrix corresponds to the moments up to degree d of a measure
    @variable(m, Y[1:numSets, 1:length(monomials)])

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
                add_to_expression!(expr, Y[el, xind] - strikes[i, j] * Y[el, end])
            end
            @constraint(m, expr == prices[i, j])
        end
    end

    @constraint(m, sum(Y[i, end] for i = 1:size(Y)[1]) == 1) #probability measure
    @constraint(
        m,
        sum(sum(Y[i, ind[2*e(j)]] for j = 1:n) for i = 1:size(Y)[1]) <= M
    ) #finite second moments



    for i = 1:length(identifier) #psd condition, localizing matrices
        push!(
            auxList,
            Array{AffExpr,2}(undef, length(refMons), length(refMons)),
        )
        for j = 1:length(refMons)
            for k = 1:length(refMons)
                auxList[length(auxList)][j, k] =
                    Y[i,ind[refMons[j]+refMons[k]]]
            end
        end
        @constraint(m, auxList[length(auxList)] in PSDCone()) #every measure must have psd moment matrix

        xvec = []

        for counter = 1:n
            push!(xvec , [
                -identifier[i][1][1][counter] * identifier[i][1][2][counter],
                identifier[i][1][1][counter] + identifier[i][1][2][counter],
                -1,
            ]
            )
        end

        for counter = 1:n
            push!(
                auxList,
                Array{AffExpr,2}(undef, length(refMons), length(refMons)),
            )

            for j = 1:length(refMons)
                for k = 1:length(refMons)
                    auxList[length(auxList)][j, k] =
                        xvec[counter][1] * (Y[i, ind[refMons[j]+refMons[k]]]) +
                        xvec[counter][2] * (Y[i, ind[e(counter)+refMons[j]+refMons[k]]]) +
                        xvec[counter][3] * (Y[i,  ind[2*e(counter)+refMons[j]+refMons[k]]])
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())

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
                        K * (Y[i, ind[refMons[j]+refMons[k]]]) - sum(w[counter2] * (Y[i, ind[e(counter2)+refMons[j]+refMons[k]]]) for counter2 = 1:n)
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())

        elseif identifier[i][2] == 2 #if split and upper (x-a)(b-x) and x+y-K >= 0




            push!(
                auxList,
                Array{AffExpr,2}(undef, length(refMons), length(refMons)),
            )
            for j = 1:length(refMons)
                for k = 1:length(refMons)
                    auxList[length(auxList)][j, k] =
                        -K * (Y[i, ind[refMons[j]+refMons[k]]]) + sum(w[counter2] * (Y[i, ind[e(counter2)+refMons[j]+refMons[k]]]) for counter2 = 1:n)
                end
            end
            @constraint(m, auxList[length(auxList)] in PSDCone())
        end

    end


    @constraint(m, Y .>= 0) #we know we are in DNN
    objSets = getObjSets(identifier)
    #display(objSets)
    obj = B*sum(
        sum(  w[j] * Y[i, ind[e(j)]] for j = 1:n )  -
        K * Y[i, ind[[0 for count = 1:n]]] for i in objSets
    )

    #get upper bound
    @objective(m, Max, obj)
    optimize!(m)
    display(termination_status(m))
    display(dual_status(m))
    display(primal_status(m))
    print("\n \n")

    print("Upper bound: ", value.(obj), "\n \n")


    #get lower bound
    @objective(m, Min, obj)
    optimize!(m)
    display(termination_status(m))
    display(dual_status(m))
    display(primal_status(m))
    print("\n \n")

    print("Lower Bound: ", value.(obj), "\n \n")


end



##
#Example strikes and prices
##

strikes = [ 100 110;
            102 107]

prices = [ 12 3;
           10 6]

weights = [1/2 1/2]

##

strikes = [ 95 100 110;
            96 102 107]

prices = [ 16 11 3;
           15 9 6]

weights = [1/2 1/2]

## Currency basket option

strikes = [ 135.5 138.5 ; #GBP/USD
            116 119 ] #EUR/USD

prices = [  2.77 1.17;
            2.21 0.67]

weights = [2/3 1/3]

## Example Bertsimas Popescu

strikes = [95 100 110 115 120]

prices = [12.875 8.375 1.875 0.625 0.25]

weights = [1]

##

compBounds(106, 1,true, strikes, prices, weights)
println("\n \n \n ")
