using JuMP
using MosekTools
using Combinatorics

# this function returns ∫x^n dν(x) = ∫x^n exp(-x)dx from k to ∞
function momMon(n,k)
    return exp(-k)*sum(factorial(n)/factorial(i)*k^i for i = 0:n)
end

#this function returns ∫m(i)*m(j)dν(x) for m(i),m(j) being the i-th (j-th) Laguerre basis elements
function momLag(i,j,k,x)
    return sum(sum(binomial(i,c1)*binomial(j,c2)*((-1)^(c1+c2))/(factorial(c1)*factorial(c2))*momMon(c1+c2+x,k) for c1 = 0:j) for c2 = 0:i)
end

#returns contraint matrix of degree r for functions of the form \max(0,x-k)
function constrMat(k,r)
    conMat = zeros(BigFloat, binomial(1+r,r),binomial(1+r,r))
    for i = 1:size(conMat)[1]
        for j = i:size(conMat)[2]
            conMat[i,j] = momLag(i,j, k,1)-k*momLag(i,j,k,0)
            conMat[j,i] = momLag(i,j, k,1)-k*momLag(i,j,k,0)
        end
    end
    return conMat
end

##


m = Model(Mosek.Optimizer)
r = 4
kmax = 110
eps = 0.0273

@variable(m, S[1:binomial(1+r,r),1:binomial(1+r,r)])
@constraint(m, S in PSDCone())

C = constrMat(105/kmax,r) #objective
A1 = constrMat(100/kmax,r)#constraint 1
A2 = constrMat(110/kmax, r)#constraint 2
P = Matrix(I, r+1, r+1)#identity


@constraint(m, tr(A1*S) >= 8.375/kmax-eps)
@constraint(m, tr(A1*S) <= 8.375/kmax+eps)

@constraint(m, tr(A2*S) >= 1.875/kmax-eps)
@constraint(m, tr(A2*S) <= 1.875/kmax+eps)


@constraint(m, tr(P*S) >= 1/kmax-eps)
@constraint(m, tr(P*S) <= 1/kmax+eps)

obj = tr(S*C)

@objective(m, Min, obj)
optimize!(m)

display(termination_status(m))
display(dual_status(m))
display(primal_status(m))

display(value.(obj)*kmax)
