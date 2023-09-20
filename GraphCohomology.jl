using Graphs, Multigraphs
using Oscar

const ℤ = ZZ

function GraphHomology(Γ::AbstractGraph{T}) where T
    numVertices, numEdges = Graphs.nv(Γ), sum(e.mul for e in Graphs.edges(Γ))
    C₀ = free_module(ℤ, numVertices)
    C₁ = free_module(ℤ, numEdges)

    edgeList = Tuple{Int, Int}[]
    for e in Graphs.edges(Γ)
        for _ in 1:(e.mul)
            push!(edgeList, (e.src, e.dst))
        end
    end 
    ϕ = hom(C₁, C₀, [C₀[v] - C₀[u] for (u, v) in edgeList])
    kernel(ϕ)
end

function GraphCohomology(Γ::AbstractGraph{T}) where T
    numVertices, numEdges = Graphs.nv(Γ), sum(e.mul for e in Graphs.edges(Γ))
    C¹ = free_module(ℤ, numEdges)
    C⁰ = free_module(ℤ, numVertices)

    vertexValue = [zero(C¹) for _ in 1:numVertices]
    Ct = 1
    for e in Graphs.edges(Γ)
        for _ in 1:(e.mul)
            vertexValue[e.src] -= C¹[Ct]
            vertexValue[e.dst] += C¹[Ct]
            Ct += 1
        end
    end
    ϕ = hom(C⁰, C¹, vertexValue)
    cokernel(ϕ)
end

function ℭ(k, l, Γ)
    k % 2 == 1 && return free_module(ℤ, 0)

    numEdges = 0 #TODO
end